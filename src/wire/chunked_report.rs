//! A wire protocol for representing Modality probe log reports
//! that are fragmented into multiple chunks due to sizing
//! constraints

use crate::ProbeId;
use byteorder::{ByteOrder, LittleEndian};
use static_assertions::const_assert_ne;

/// Everything that can go wrong when attempting to interpret a chunked report
/// from the wire representation
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ChunkedReportWireError {
    /// The fingerprint didn't match expectations
    InvalidFingerprint,
    /// There weren't enough bytes for a full header
    MissingHeader,
    /// There weren't enough payload bytes (based on
    /// expectations from inspecting the header).
    IncompletePayload,
    /// The header supplied a n_payload_bytes value
    /// greater than the allowed maximum, `MAX_PAYLOAD_BYTES_PER_CHUNK`
    TooManyPayloadBytes,
    /// The data type was not one of the supported varieties
    UnsupportedDataType(u8),
    /// The probe id didn't follow the rules for being
    /// a valid Modality probe-specifying ProbeId
    InvalidProbeId(u32),
}

/// Chunked reports carry payloads, but we need a hint to figure out how to interpret it.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ChunkPayloadDataType {
    /// Compact log data. An order-sensitive slice of (little-endian) u32s.
    Log,
    /// Extension data. Opaque bytes.
    Extension,
}

impl ChunkPayloadDataType {
    fn data_type_le_byte(self) -> u8 {
        match self {
            ChunkPayloadDataType::Log => ChunkedReport::<&[u8]>::DATA_TYPE_LOG.to_le(),
            ChunkPayloadDataType::Extension => ChunkedReport::<&[u8]>::DATA_TYPE_EXTENSION.to_le(),
        }
    }
}

/// A read/write wrapper around a chunked report buffer
#[derive(Debug, Clone)]
pub struct ChunkedReport<T: AsRef<[u8]>> {
    buffer: T,
}

mod field {
    type Field = ::core::ops::Range<usize>;
    type Rest = ::core::ops::RangeFrom<usize>;

    /// A magical (constant) value used as a hint about the
    /// data encoded in this pile of bytes.
    pub const FINGERPRINT: Field = 0..4;
    /// A u32 representing the probe_id of the
    /// Modality probe instance producing this report.
    pub const PROBE_ID: Field = 4..8;
    /// A u16 representing the group of report chunks to which
    /// this chunk belongs. Determined by the Modality probe instance.
    /// Expected, but not guaranteed to be increasing
    /// and wrapping-overflowing during the lifetime of an Modality probe
    /// instance.
    ///
    /// Erring on the side of a large
    /// number of these to support cases like:
    ///   * a long-lasting partition from the report collector whilst reports
    /// are archived for future sending
    ///   * a very high report production cadence relative to the transmission cadence
    pub const CHUNK_GROUP_ID: Field = 8..10;
    /// In what ordinal position does this chunk's payload live relative to the other chunks.
    pub const CHUNK_INDEX: Field = 10..12;
    /// Does this chunk's payload contain log data (0x01) or extension data (0x02)?
    pub const PAYLOAD_DATA_TYPE: usize = 12;
    /// Is this chunk the last chunk in the report (0x01) or not (0x00)?
    pub const IS_LAST_CHUNK: usize = 13;
    /// Reserved for future enhancements and to make the payload 4-byte aligned
    ///
    /// Note that in general, the three bytes of data currently encoding
    /// `payload_data_type`, `is_last_chunk`, and `reserved`, are ripe for future
    /// compaction for bit-field use.
    pub const RESERVED: usize = 14;
    /// How many of the payload bytes are populated?
    pub const N_CHUNK_PAYLOAD_BYTES: usize = 15;
    /// The payload, consists of either log bytes, or extension bytes
    pub const PAYLOAD: Rest = 16..;
}

const_assert_ne!(
    ChunkedReport::<&[u8]>::DATA_TYPE_LOG,
    ChunkedReport::<&[u8]>::DATA_TYPE_EXTENSION
);

impl<T: AsRef<[u8]>> ChunkedReport<T> {
    /// Chunked report fingerprint (ECNK)
    pub const FINGERPRINT: u32 = 0x45_43_4E_4B;

    /// The size of a chunk in bytes
    pub const MAX_CHUNK_BYTES: usize = 256;

    pub(super) const DATA_TYPE_LOG: u8 = 0b0001;
    pub(super) const DATA_TYPE_EXTENSION: u8 = 0b0010;

    /// The maximum number of payload bytes possibly populated
    /// within a chunk.
    pub const MAX_PAYLOAD_BYTES_PER_CHUNK: usize = 256 - field::PAYLOAD.start;

    /// Construct a chunked report from a byte buffer
    pub fn new_unchecked(buffer: T) -> ChunkedReport<T> {
        ChunkedReport { buffer }
    }

    /// Construct a chunked report from a byte buffer, with checks.
    ///
    /// A combination of:
    /// * [new_unchecked](struct.ChunkedReport.html#method.new_unchecked)
    /// * [check_len](struct.ChunkedReport.html#method.check_len)
    /// * [check_fingerprint](struct.ChunkedReport.html#method.check_fingerprint)
    /// * [check_payload_len](struct.ChunkedReport.html#method.check_payload_len)
    pub fn new(buffer: T) -> Result<ChunkedReport<T>, ChunkedReportWireError> {
        let r = Self::new_unchecked(buffer);
        r.check_len()?;
        r.check_fingerprint()?;
        r.check_payload_len()?;
        Ok(r)
    }

    /// Ensure that no accessor method will panic if called.
    ///
    /// Returns `Err(ChunkedReportWireError::MissingHeader)` if the buffer
    /// is too short.
    pub fn check_len(&self) -> Result<(), ChunkedReportWireError> {
        let len = self.buffer.as_ref().len();
        if len < field::PAYLOAD.start {
            Err(ChunkedReportWireError::MissingHeader)
        } else {
            Ok(())
        }
    }

    /// Check for the expected fingerprint value.
    ///
    /// Returns `Err(ChunkedReportWireError::InvalidFingerprint)` if the fingerprint
    /// does not match.
    pub fn check_fingerprint(&self) -> Result<(), ChunkedReportWireError> {
        if self.fingerprint() != Self::FINGERPRINT {
            Err(ChunkedReportWireError::InvalidFingerprint)
        } else {
            Ok(())
        }
    }

    /// Ensure the payload size is sufficient to hold bytes according to the header
    /// field `n_chunk_payload_bytes`.
    ///
    /// Returns `Err(ChunkedReportWireError::IncompletePayload)` if the buffer
    /// is too short, and `Err(ChunkedReportWireError::TooManyPayloadBytes)` if
    /// `n_chunk_payload_bytes` exceeds `MAX_PAYLOAD_BYTES_PER_CHUNK`.
    pub fn check_payload_len(&self) -> Result<(), ChunkedReportWireError> {
        let n_chunk_payload_bytes = self.n_chunk_payload_bytes() as usize;
        let len = self.buffer.as_ref().len();
        if len < (field::PAYLOAD.start + n_chunk_payload_bytes) {
            Err(ChunkedReportWireError::IncompletePayload)
        } else if n_chunk_payload_bytes > Self::MAX_PAYLOAD_BYTES_PER_CHUNK {
            Err(ChunkedReportWireError::TooManyPayloadBytes)
        } else {
            Ok(())
        }
    }

    /// Consumes the chunked report, returning the underlying buffer
    pub fn into_inner(self) -> T {
        self.buffer
    }

    /// Return the length of a chunked report header
    pub fn header_len() -> usize {
        field::PAYLOAD.start
    }

    /// Return the length of a buffer required to hold a chunked report
    /// with a payload length of `n_chunk_payload_bytes`
    pub fn buffer_len(n_chunk_payload_bytes: usize) -> usize {
        field::PAYLOAD.start + n_chunk_payload_bytes
    }

    /// Return the length of the chunked report payload
    pub fn payload_len(&self) -> usize {
        self.n_chunk_payload_bytes() as usize
    }

    /// Return the `fingerprint` field
    #[inline]
    pub fn fingerprint(&self) -> u32 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u32(&data[field::FINGERPRINT])
    }

    /// Return the `probe_id` field
    #[inline]
    pub fn probe_id(&self) -> Result<ProbeId, ChunkedReportWireError> {
        let data = self.buffer.as_ref();
        let raw_probe_id = LittleEndian::read_u32(&data[field::PROBE_ID]);
        match ProbeId::new(raw_probe_id) {
            Some(id) => Ok(id),
            None => Err(ChunkedReportWireError::InvalidProbeId(raw_probe_id)),
        }
    }

    /// Return the `chunk_group_id` field
    #[inline]
    pub fn chunk_group_id(&self) -> u16 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u16(&data[field::CHUNK_GROUP_ID])
    }

    /// Return the `chunk_index` field
    #[inline]
    pub fn chunk_index(&self) -> u16 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u16(&data[field::CHUNK_INDEX])
    }

    /// Return the `payload_data_type` field
    #[inline]
    pub fn payload_data_type(&self) -> Result<ChunkPayloadDataType, ChunkedReportWireError> {
        let data = self.buffer.as_ref();
        match data[field::PAYLOAD_DATA_TYPE] {
            Self::DATA_TYPE_LOG => Ok(ChunkPayloadDataType::Log),
            Self::DATA_TYPE_EXTENSION => Ok(ChunkPayloadDataType::Extension),
            b => Err(ChunkedReportWireError::UnsupportedDataType(b)),
        }
    }

    /// Return the `is_last_chunk` field
    #[inline]
    pub fn is_last_chunk(&self) -> bool {
        let data = self.buffer.as_ref();
        data[field::IS_LAST_CHUNK] != 0
    }

    /// Return the `reserved` field
    #[inline]
    pub fn reserved(&self) -> u8 {
        let data = self.buffer.as_ref();
        data[field::RESERVED]
    }

    /// Return the `n_chunk_payload_bytes` field
    #[inline]
    pub fn n_chunk_payload_bytes(&self) -> u8 {
        let data = self.buffer.as_ref();
        data[field::N_CHUNK_PAYLOAD_BYTES]
    }
}

impl<'a, T: AsRef<[u8]> + ?Sized> ChunkedReport<&'a T> {
    /// Return a pointer to the payload
    #[inline]
    pub fn payload(&self) -> &'a [u8] {
        let data = self.buffer.as_ref();
        &data[field::PAYLOAD]
    }
}

impl<T: AsRef<[u8]> + AsMut<[u8]>> ChunkedReport<T> {
    /// Set the `fingerprint` field to
    /// [Self::FINGERPRINT](struct.ChunkedReport.html#associatedconstant.FINGERPRINT)
    #[inline]
    pub fn set_fingerprint(&mut self) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::FINGERPRINT], Self::FINGERPRINT);
    }

    /// Set the `probe_id` field
    #[inline]
    pub fn set_probe_id(&mut self, value: ProbeId) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::PROBE_ID], value.get_raw());
    }

    /// Set the `chunk_group_id` field
    #[inline]
    pub fn set_chunk_group_id(&mut self, value: u16) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u16(&mut data[field::CHUNK_GROUP_ID], value);
    }

    /// Set the `chunk_index` field
    #[inline]
    pub fn set_chunk_index(&mut self, value: u16) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u16(&mut data[field::CHUNK_INDEX], value);
    }

    /// Set the `payload_data_type` field
    #[inline]
    pub fn set_payload_data_type(&mut self, value: ChunkPayloadDataType) {
        let data = self.buffer.as_mut();
        data[field::PAYLOAD_DATA_TYPE] = value.data_type_le_byte();
    }

    /// Set the `is_last_chunk` field
    #[inline]
    pub fn set_is_last_chunk(&mut self, value: bool) {
        let data = self.buffer.as_mut();
        data[field::IS_LAST_CHUNK] = u8::from(value);
    }

    /// Set the `reserved` field
    #[inline]
    pub fn set_reserved(&mut self, value: u8) {
        let data = self.buffer.as_mut();
        data[field::RESERVED] = value;
    }

    /// Set the `n_chunk_payload_bytes` field
    #[inline]
    pub fn set_n_chunk_payload_bytes(&mut self, value: u8) {
        let data = self.buffer.as_mut();
        data[field::N_CHUNK_PAYLOAD_BYTES] = value;
    }

    /// Return a mutable pointer to the payload
    #[inline]
    pub fn payload_mut(&mut self) -> &mut [u8] {
        let data = self.buffer.as_mut();
        &mut data[field::PAYLOAD]
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for ChunkedReport<T> {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    static MSG_BYTES: [u8; 28] = [
        // fingerprint
        0x4B, 0x4E, 0x43, 0x45,
        // probe_id: 1
        0x01, 0x00, 0x00, 0x00,
        // chunk_group_id: 2
        0x02, 0x00,
        // chunk_index: 3,
        0x03, 0x00,
        // payload_data_type: 1
        0x01,
        // is_last_chunk: 0,
        0x00,
        // reserved: 0
        0x00,
        // n_chunk_payload_bytes: 12
        0x0C,
        // payload
        0x03, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00,
    ];

    #[rustfmt::skip]
    static PAYLOAD_BYTES: [u8; 12] = [
        0x03, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00,
    ];

    #[test]
    fn header_len() {
        assert_eq!(ChunkedReport::<&[u8]>::header_len(), 16);
        let n_chunk_payload_bytes = 12;
        assert_eq!(
            ChunkedReport::<&[u8]>::buffer_len(n_chunk_payload_bytes),
            16 + 12
        );
    }

    #[test]
    fn construct() {
        let mut bytes = [0xFF; 28];
        let mut r = ChunkedReport::new_unchecked(&mut bytes[..]);
        assert_eq!(r.check_len(), Ok(()));
        r.set_fingerprint();
        r.set_probe_id(ProbeId::new(1).unwrap());
        r.set_chunk_group_id(2);
        r.set_chunk_index(3);
        r.set_payload_data_type(ChunkPayloadDataType::Log);
        r.set_is_last_chunk(false);
        r.set_reserved(0);
        r.set_n_chunk_payload_bytes(12);
        r.payload_mut().copy_from_slice(&PAYLOAD_BYTES[..]);
        assert_eq!(r.check_fingerprint(), Ok(()));
        assert_eq!(r.check_payload_len(), Ok(()));
        assert_eq!(&r.into_inner()[..], &MSG_BYTES[..]);
    }

    #[test]
    fn construct_with_extra() {
        const EXTRA_JUNK_SIZE: usize = 7;
        let mut bytes = [0xFF; 28 + EXTRA_JUNK_SIZE];
        let mut r = ChunkedReport::new_unchecked(&mut bytes[..]);
        assert_eq!(r.check_len(), Ok(()));
        r.set_fingerprint();
        r.set_probe_id(ProbeId::new(1).unwrap());
        r.set_chunk_group_id(2);
        r.set_chunk_index(3);
        r.set_payload_data_type(ChunkPayloadDataType::Log);
        r.set_is_last_chunk(false);
        r.set_reserved(0);
        r.set_n_chunk_payload_bytes(12);
        assert_eq!(r.payload_len(), 12);
        assert_eq!(r.payload_mut().len(), 12 + EXTRA_JUNK_SIZE);
        let payload_len = r.payload_len();
        (&mut r.payload_mut()[..payload_len]).copy_from_slice(&PAYLOAD_BYTES[..]);
        assert_eq!(r.check_fingerprint(), Ok(()));
        assert_eq!(r.check_payload_len(), Ok(()));
        let msg_len = ChunkedReport::<&[u8]>::buffer_len(12);
        assert_eq!(&r.into_inner()[..msg_len], &MSG_BYTES[..]);
    }

    #[test]
    fn deconstruct() {
        let r = ChunkedReport::new(&MSG_BYTES[..]).unwrap();
        assert_eq!(r.fingerprint(), ChunkedReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id().unwrap().get_raw(), 1);
        assert_eq!(r.chunk_group_id(), 2);
        assert_eq!(r.chunk_index(), 3);
        assert_eq!(r.payload_data_type(), Ok(ChunkPayloadDataType::Log));
        assert_eq!(r.is_last_chunk(), false);
        assert_eq!(r.reserved(), 0);
        assert_eq!(r.n_chunk_payload_bytes(), 12);
        assert_eq!(r.payload_len(), 12);
        assert_eq!(r.payload(), &PAYLOAD_BYTES[..]);
    }

    #[test]
    fn deconstruct_with_extra() {
        const EXTRA_JUNK_SIZE: usize = 7;
        let mut bytes = [0xFF; 28 + EXTRA_JUNK_SIZE];
        assert_eq!(bytes.len(), MSG_BYTES.len() + EXTRA_JUNK_SIZE);
        (&mut bytes[..28]).copy_from_slice(&MSG_BYTES[..]);
        let r = ChunkedReport::new(&bytes[..]).unwrap();
        assert_eq!(r.fingerprint(), ChunkedReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id().unwrap().get_raw(), 1);
        assert_eq!(r.chunk_group_id(), 2);
        assert_eq!(r.chunk_index(), 3);
        assert_eq!(r.payload_data_type(), Ok(ChunkPayloadDataType::Log));
        assert_eq!(r.is_last_chunk(), false);
        assert_eq!(r.reserved(), 0);
        assert_eq!(r.n_chunk_payload_bytes(), 12);
        assert_eq!(r.payload_len(), 12);
        assert_eq!(r.payload().len(), 12 + EXTRA_JUNK_SIZE);
        let payload_len = r.payload_len();
        assert_eq!(&r.payload()[..payload_len], &PAYLOAD_BYTES[..]);
    }

    #[test]
    fn invalid_fingerprint() {
        let bytes = [0xFF; 16];
        let r = ChunkedReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ChunkedReportWireError::InvalidFingerprint);
    }

    #[test]
    fn missing_header() {
        let bytes = [0xFF; 16 - 1];
        assert_eq!(bytes.len(), ChunkedReport::<&[u8]>::header_len() - 1);
        let r = ChunkedReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ChunkedReportWireError::MissingHeader);
    }

    #[test]
    fn incomplete_payload() {
        let mut bytes = MSG_BYTES.clone();
        let mut r = ChunkedReport::new(&mut bytes[..]).unwrap();
        assert!(MSG_BYTES.len() < (ChunkedReport::<&[u8]>::MAX_CHUNK_BYTES - 1));
        r.set_n_chunk_payload_bytes(MSG_BYTES.len() as u8 + 1);
        let bytes = r.into_inner();
        let r = ChunkedReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ChunkedReportWireError::IncompletePayload);
    }

    #[test]
    fn too_many_payload_bytes() {
        const EXTRA_JUNK_SIZE: usize = 256;
        let mut bytes = [0xFF; 28 + EXTRA_JUNK_SIZE];
        assert_eq!(bytes.len(), MSG_BYTES.len() + EXTRA_JUNK_SIZE);
        (&mut bytes[..28]).copy_from_slice(&MSG_BYTES[..]);
        let mut r = ChunkedReport::new(&mut bytes[..]).unwrap();
        r.set_n_chunk_payload_bytes(ChunkedReport::<&[u8]>::MAX_PAYLOAD_BYTES_PER_CHUNK as u8 + 1);
        let bytes = r.into_inner();
        let r = ChunkedReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ChunkedReportWireError::TooManyPayloadBytes);
    }
}
