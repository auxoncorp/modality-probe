//! A wire protocol for representing Modality probe log reports in bulk form

use byteorder::{ByteOrder, LittleEndian};

/// Everything that can go wrong when attempting to interpret a bulk report
/// from the wire representation
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BulkReportWireError {
    /// The fingerprint didn't match expectations
    InvalidFingerprint,
    /// There weren't enough bytes for a full header
    MissingHeader,
    /// There weren't enough payload bytes (based on
    /// expectations from inspecting the header).
    IncompletePayload,
}

/// A read/write wrapper around a bulk report buffer
#[derive(Debug, Clone)]
pub struct BulkReport<T: AsRef<[u8]>> {
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
    /// How many of the payload bytes are populated with log data?
    pub const N_LOG_BYTES: Field = 8..12;
    /// How many of the payload bytes are populated with extension data?
    pub const N_EXT_BYTES: Field = 12..16;
    /// The payload, consists of (in order):
    /// * Log bytes: sequence of CompactLogItem ([u32])
    /// * Extension bytes: sequence of u8
    pub const PAYLOAD: Rest = 16..;
}

impl<T: AsRef<[u8]>> BulkReport<T> {
    /// Bulk report fingerprint (EBLK)
    pub const FINGERPRINT: u32 = 0x45_42_4C_4B;

    /// Construct a bulk report from a byte buffer
    pub fn new_unchecked(buffer: T) -> BulkReport<T> {
        BulkReport { buffer }
    }

    /// Construct a bulk report from a byte buffer, with checks.
    ///
    /// A combination of:
    /// * [new_unchecked](struct.BulkReport.html#method.new_unchecked)
    /// * [check_len](struct.BulkReport.html#method.check_len)
    /// * [check_fingerprint](struct.BulkReport.html#method.check_fingerprint)
    /// * [check_payload_len](struct.BulkReport.html#method.check_payload_len)
    pub fn new_checked(buffer: T) -> Result<BulkReport<T>, BulkReportWireError> {
        let r = Self::new_unchecked(buffer);
        r.check_len()?;
        r.check_fingerprint()?;
        r.check_payload_len()?;
        Ok(r)
    }

    /// Ensure that no accessor method will panic if called.
    ///
    /// Returns `Err(BulkReportWireError::MissingHeader)` if the buffer
    /// is too short.
    pub fn check_len(&self) -> Result<(), BulkReportWireError> {
        let len = self.buffer.as_ref().len();
        if len < field::PAYLOAD.start {
            Err(BulkReportWireError::MissingHeader)
        } else {
            Ok(())
        }
    }

    /// Check for the expected fingerprint value.
    ///
    /// Returns `Err(BulkReportWireError::InvalidFingerprint)` if the fingerprint
    /// does not match.
    pub fn check_fingerprint(&self) -> Result<(), BulkReportWireError> {
        if self.fingerprint() != Self::FINGERPRINT {
            Err(BulkReportWireError::InvalidFingerprint)
        } else {
            Ok(())
        }
    }

    /// Ensure the payload size is sufficient to hold bytes according to the header
    /// fields `n_log_bytes` and `n_extension_bytes`.
    ///
    /// Returns `Err(BulkReportWireError::IncompletePayload)` if the buffer
    /// is too short.
    pub fn check_payload_len(&self) -> Result<(), BulkReportWireError> {
        let n_log_bytes = self.n_log_bytes() as usize;
        let n_extension_bytes = self.n_extension_bytes() as usize;
        let len = self.buffer.as_ref().len();
        if len < (field::PAYLOAD.start + n_log_bytes + n_extension_bytes) {
            Err(BulkReportWireError::IncompletePayload)
        } else {
            Ok(())
        }
    }

    /// Consumes the bulk report, returning the underlying buffer
    pub fn into_inner(self) -> T {
        self.buffer
    }

    /// Return the length of a bulk report header
    pub fn header_len() -> usize {
        field::PAYLOAD.start
    }

    /// Return the length of a buffer required to hold a bulk report
    /// with a payload length of `n_log_bytes` + `n_extension_bytes`
    pub fn buffer_len(n_log_bytes: usize, n_extension_bytes: usize) -> usize {
        field::PAYLOAD.start + n_log_bytes + n_extension_bytes
    }

    /// Return the length of the bulk report payload
    pub fn payload_len(&self) -> usize {
        let n_log_bytes = self.n_log_bytes() as usize;
        let n_extension_bytes = self.n_extension_bytes() as usize;
        n_log_bytes + n_extension_bytes
    }

    /// Return the `fingerprint` field
    #[inline]
    pub fn fingerprint(&self) -> u32 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u32(&data[field::FINGERPRINT])
    }

    /// Return the `probe_id` field
    #[inline]
    pub fn probe_id(&self) -> u32 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u32(&data[field::PROBE_ID])
    }

    /// Return the `n_log_bytes` field
    #[inline]
    pub fn n_log_bytes(&self) -> u32 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u32(&data[field::N_LOG_BYTES])
    }

    /// Return the `n_extension_bytes` field
    #[inline]
    pub fn n_extension_bytes(&self) -> u32 {
        let data = self.buffer.as_ref();
        LittleEndian::read_u32(&data[field::N_EXT_BYTES])
    }
}

impl<'a, T: AsRef<[u8]> + ?Sized> BulkReport<&'a T> {
    /// Return a pointer to the payload
    #[inline]
    pub fn payload(&self) -> &'a [u8] {
        let data = self.buffer.as_ref();
        &data[field::PAYLOAD]
    }
}

impl<T: AsRef<[u8]> + AsMut<[u8]>> BulkReport<T> {
    /// Set the `fingerprint` field
    #[inline]
    pub fn set_fingerprint(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::FINGERPRINT], value);
    }

    /// Set the `probe_id` field
    #[inline]
    pub fn set_probe_id(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::PROBE_ID], value);
    }

    /// Set the `n_log_bytes` field
    #[inline]
    pub fn set_n_log_bytes(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::N_LOG_BYTES], value);
    }

    /// Set the `n_extension_bytes` field
    #[inline]
    pub fn set_n_extension_bytes(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        LittleEndian::write_u32(&mut data[field::N_EXT_BYTES], value);
    }

    /// Return a mutable pointer to the payload
    #[inline]
    pub fn payload_mut(&mut self) -> &mut [u8] {
        let data = self.buffer.as_mut();
        &mut data[field::PAYLOAD]
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for BulkReport<T> {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl<T: AsRef<[u8]> + AsMut<[u8]>> AsMut<[u8]> for BulkReport<T> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.buffer.as_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    static MSG_BYTES: [u8; 28] = [
        // fingerprint
        0x4B, 0x4C, 0x42, 0x45,
        // probe_id: 1
        0x01, 0x00, 0x00, 0x00,
        // n_log_bytes: 8
        0x08, 0x00, 0x00, 0x00,
        // n_extension_bytes: 4
        0x04, 0x00, 0x00, 0x00,
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
        assert_eq!(BulkReport::<&[u8]>::header_len(), 16);
        let n_log_bytes = 12;
        let n_ext_bytes = 14;
        assert_eq!(
            BulkReport::<&[u8]>::buffer_len(n_log_bytes, n_ext_bytes),
            16 + 12 + 14
        );
    }

    #[test]
    fn construct() {
        let mut bytes = [0xFF; 28];
        let mut r = BulkReport::new_unchecked(&mut bytes[..]);
        assert_eq!(r.check_len(), Ok(()));
        r.set_fingerprint(BulkReport::<&[u8]>::FINGERPRINT);
        r.set_probe_id(1);
        r.set_n_log_bytes(8);
        r.set_n_extension_bytes(4);
        r.payload_mut().copy_from_slice(&PAYLOAD_BYTES[..]);
        assert_eq!(r.check_fingerprint(), Ok(()));
        assert_eq!(r.check_payload_len(), Ok(()));
        assert_eq!(&r.into_inner()[..], &MSG_BYTES[..]);
    }

    #[test]
    fn construct_with_extra() {
        const EXTRA_JUNK_SIZE: usize = 7;
        let mut bytes = [0xFF; 28 + EXTRA_JUNK_SIZE];
        let mut r = BulkReport::new_unchecked(&mut bytes[..]);
        assert_eq!(r.check_len(), Ok(()));
        r.set_fingerprint(BulkReport::<&[u8]>::FINGERPRINT);
        r.set_probe_id(1);
        r.set_n_log_bytes(8);
        r.set_n_extension_bytes(4);
        assert_eq!(r.payload_len(), 8 + 4);
        assert_eq!(r.payload_mut().len(), 8 + 4 + EXTRA_JUNK_SIZE);
        let payload_len = r.payload_len();
        (&mut r.payload_mut()[..payload_len]).copy_from_slice(&PAYLOAD_BYTES[..]);
        assert_eq!(r.check_fingerprint(), Ok(()));
        assert_eq!(r.check_payload_len(), Ok(()));
        let msg_len = BulkReport::<&[u8]>::buffer_len(8, 4);
        assert_eq!(&r.into_inner()[..msg_len], &MSG_BYTES[..]);
    }

    #[test]
    fn deconstruct() {
        let r = BulkReport::new_checked(&MSG_BYTES[..]).unwrap();
        assert_eq!(r.fingerprint(), BulkReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id(), 1);
        assert_eq!(r.n_log_bytes(), 8);
        assert_eq!(r.n_extension_bytes(), 4);
        assert_eq!(r.payload_len(), 8 + 4);
        assert_eq!(r.payload(), &PAYLOAD_BYTES[..]);
        let n_log_bytes = r.n_log_bytes();
        let (log_bytes, ext_bytes) = r.payload().split_at(n_log_bytes as usize);
        assert_eq!(log_bytes, [0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00]);
        assert_eq!(ext_bytes, [0x05, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn deconstruct_with_extra() {
        const EXTRA_JUNK_SIZE: usize = 7;
        let mut bytes = [0xFF; 28 + EXTRA_JUNK_SIZE];
        assert_eq!(bytes.len(), MSG_BYTES.len() + EXTRA_JUNK_SIZE);
        (&mut bytes[..28]).copy_from_slice(&MSG_BYTES[..]);
        let r = BulkReport::new_checked(&bytes[..]).unwrap();
        assert_eq!(r.fingerprint(), BulkReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id(), 1);
        assert_eq!(r.n_log_bytes(), 8);
        assert_eq!(r.n_extension_bytes(), 4);
        assert_eq!(r.payload_len(), 8 + 4);
        assert_eq!(r.payload().len(), 8 + 4 + EXTRA_JUNK_SIZE);
        let payload_len = r.payload_len();
        assert_eq!(&r.payload()[..payload_len], &PAYLOAD_BYTES[..]);
    }

    #[test]
    fn invalid_fingerprint() {
        let bytes = [0xFF; 16];
        let r = BulkReport::new_checked(&bytes[..]);
        assert_eq!(r.unwrap_err(), BulkReportWireError::InvalidFingerprint);
    }

    #[test]
    fn missing_header() {
        let bytes = [0xFF; 16 - 1];
        assert_eq!(bytes.len(), BulkReport::<&[u8]>::header_len() - 1);
        let r = BulkReport::new_checked(&bytes[..]);
        assert_eq!(r.unwrap_err(), BulkReportWireError::MissingHeader);
    }

    #[test]
    fn incomplete_payload() {
        let mut bytes = MSG_BYTES.clone();
        let mut r = BulkReport::new_checked(&mut bytes[..]).unwrap();
        r.set_n_log_bytes(8 + 1);
        r.set_n_extension_bytes(4 + 1);
        let bytes = r.into_inner();
        let r = BulkReport::new_checked(&bytes[..]);
        assert_eq!(r.unwrap_err(), BulkReportWireError::IncompletePayload);
    }
}
