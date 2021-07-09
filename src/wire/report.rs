//! A wire protocol for representing Modality probe log reports.
//! A report is a section of the probe's event log prepended by
//! the most up-to-date neighbor clocks UP TO that report.

use crate::{
    log::LogEntry,
    time::{NanosecondResolution, WallClockId},
    wire::le_bytes,
    LogicalClock, ProbeId,
};
use core::mem;
use static_assertions::assert_eq_size;

assert_eq_size!(LogEntry, u32);

/// A log report sequence number
/// The nth report the probe has produced in its current
/// instantiation.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct SequenceNumber(pub u64);

impl From<u64> for SequenceNumber {
    fn from(v: u64) -> Self {
        SequenceNumber(v)
    }
}

impl From<SequenceNumber> for u64 {
    fn from(v: SequenceNumber) -> Self {
        v.0
    }
}

/// Everything that can go wrong when attempting to interpret a
/// report from the wire representation
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ReportWireError {
    /// The fingerprint didn't match expectations
    InvalidFingerprint,
    /// There weren't enough bytes for a full header
    MissingHeader,
    /// There weren't enough payload bytes (based on
    /// expectations from inspecting the header).
    IncompletePayload,
    /// The probe id didn't follow the rules for being
    /// a valid Modality probe-specifying ProbeId
    InvalidProbeId(u32),
}

#[cfg(feature = "std")]
impl std::error::Error for ReportWireError {}

impl core::fmt::Display for ReportWireError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ReportWireError::InvalidFingerprint => f.write_str("Invalid Fingerprint"),
            ReportWireError::MissingHeader => f.write_str("Missing Header"),
            ReportWireError::IncompletePayload => f.write_str("Incomplete Payload"),
            ReportWireError::InvalidProbeId(x) => write!(f, "Invalid Probe Id: 0x{:x}", x),
        }
    }
}

/// A read/write wrapper around a report buffer
#[derive(Debug, Clone)]
pub struct WireReport<T: AsRef<[u8]>> {
    buffer: T,
}

mod field {
    type Field = ::core::ops::Range<usize>;
    type Rest = ::core::ops::RangeFrom<usize>;

    /// A magical (constant) value used as a hint about the data
    /// encoded in this pile of bytes.
    pub const FINGERPRINT: Field = 0..4;
    /// A u32 representing the probe_id of the Modality probe instance
    /// producing this report.
    pub const PROBE_ID: Field = 4..8;
    /// The packed logical clock word for the probe at the time that this
    /// report was created.
    pub const CLOCK: Field = 8..12;
    /// The sequence number of the report.
    pub const SEQ_NUM: Field = 12..20;
    /// Whether or not this probe is using persistent epoch/restart tracking.
    pub const PERSISTENT_EPOCH_COUNTING: usize = 20;
    /// The user-provided time resolution
    pub const TIME_RESOLUTION: Field = 21..25;
    /// The user-provided wall clock id
    pub const WALL_CLOCK_ID: Field = 25..27;
    /// The number of frontier clocks present in the payload.
    ///
    /// Note: These are at the front of the payload and are specially
    /// encoded as frontier clocks.
    pub const N_CLOCKS: Field = 27..29;
    /// The number of log entries present in the payload.
    pub const N_LOG_ENTRIES: Field = 29..33;
    /// The payload, consists of (in order):
    /// * Frontier clocks
    /// * Log entries
    pub const PAYLOAD: Rest = 33..;
}

impl<T: AsRef<[u8]>> WireReport<T> {
    /// Report fingerprint (MRPT)
    pub const FINGERPRINT: u32 = 0x4D_52_50_54;

    /// Construct a report from a byte buffer
    pub fn new_unchecked(buffer: T) -> WireReport<T> {
        WireReport { buffer }
    }

    /// Construct a report from a byte buffer, with checks.
    ///
    /// A combination of:
    /// * [new_unchecked](struct.WireReport.html#method.new_unchecked)
    /// * [check_len](struct.WireReport.html#method.check_len)
    /// * [check_fingerprint](struct.WireReport.html#method.check_fingerprint)
    /// * [check_payload_len](struct.WireReport.html#method.check_payload_len)
    pub fn new(buffer: T) -> Result<Self, ReportWireError> {
        let r = Self::new_unchecked(buffer);
        r.check_len()?;
        r.check_fingerprint()?;
        r.check_payload_len()?;
        Ok(r)
    }

    /// Ensure that no accessor method will panic if called.
    ///
    /// Returns `Err(ReportWireError::MissingHeader)` if the buffer
    /// is too short.
    pub fn check_len(&self) -> Result<(), ReportWireError> {
        let len = self.buffer.as_ref().len();
        if len < field::PAYLOAD.start {
            Err(ReportWireError::MissingHeader)
        } else {
            Ok(())
        }
    }

    /// Check for the expected fingerprint value.
    ///
    /// Returns `Err(ReportWireError::InvalidFingerprint)` if the fingerprint
    /// does not match.
    pub fn check_fingerprint(&self) -> Result<(), ReportWireError> {
        if self.fingerprint() != Self::FINGERPRINT {
            Err(ReportWireError::InvalidFingerprint)
        } else {
            Ok(())
        }
    }

    /// Ensure the payload size is sufficient to hold bytes according to the header
    /// fields `n_clocks` and `n_log_entries`.
    ///
    /// Returns `Err(ReportWireError::IncompletePayload)` if the buffer
    /// is too short.
    pub fn check_payload_len(&self) -> Result<(), ReportWireError> {
        let payload_len = self.payload_len();
        let len = self.buffer.as_ref().len();
        if len < (field::PAYLOAD.start + payload_len) {
            Err(ReportWireError::IncompletePayload)
        } else {
            Ok(())
        }
    }

    /// Consumes the report, returning the underlying buffer
    pub fn into_inner(self) -> T {
        self.buffer
    }

    /// Return the length of a report header
    pub fn header_len() -> usize {
        field::PAYLOAD.start
    }

    /// Return the length of a buffer required to hold a report
    /// with a payload of `n_clocks` + `n_log_entries`
    pub fn buffer_len(n_clocks: usize, n_log_entries: usize) -> usize {
        field::PAYLOAD.start
            + (n_clocks * mem::size_of::<LogicalClock>())
            + (n_log_entries * mem::size_of::<LogEntry>())
    }

    /// Return the length of the report payload
    pub fn payload_len(&self) -> usize {
        let n_clock_bytes = self.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let n_log_bytes = self.n_log_entries() as usize * mem::size_of::<LogEntry>();
        n_clock_bytes + n_log_bytes
    }

    /// Return the `fingerprint` field
    #[inline]
    pub fn fingerprint(&self) -> u32 {
        let data = self.buffer.as_ref();
        le_bytes::read_u32(&data[field::FINGERPRINT])
    }

    /// Return the `probe_id` field
    #[inline]
    pub fn probe_id(&self) -> Result<ProbeId, ReportWireError> {
        let data = self.buffer.as_ref();
        let raw_probe_id = le_bytes::read_u32(&data[field::PROBE_ID]);
        match ProbeId::new(raw_probe_id) {
            Some(id) => Ok(id),
            None => Err(ReportWireError::InvalidProbeId(raw_probe_id)),
        }
    }

    /// Return the `clock` field
    #[inline]
    pub fn clock(&self) -> u32 {
        let data = self.buffer.as_ref();
        le_bytes::read_u32(&data[field::CLOCK])
    }

    /// Return the `seq_num` field
    #[inline]
    pub fn seq_num(&self) -> SequenceNumber {
        let data = self.buffer.as_ref();
        SequenceNumber(le_bytes::read_u64(&data[field::SEQ_NUM]))
    }

    /// Return the `persistent_epoch_counting` field
    #[inline]
    pub fn persistent_epoch_counting(&self) -> bool {
        let data = self.buffer.as_ref();
        data[field::PERSISTENT_EPOCH_COUNTING] != 0
    }

    /// Return the raw value `persistent_epoch_counting` field
    #[inline]
    pub fn raw_persistent_epoch_counting(&self) -> u8 {
        let data = self.buffer.as_ref();
        data[field::PERSISTENT_EPOCH_COUNTING]
    }

    /// Return the `time_resolution` field
    #[inline]
    pub fn time_resolution(&self) -> NanosecondResolution {
        let data = self.buffer.as_ref();
        NanosecondResolution(le_bytes::read_u32(&data[field::TIME_RESOLUTION]))
    }

    /// Return the `wall_clock_id` field
    #[inline]
    pub fn wall_clock_id(&self) -> WallClockId {
        let data = self.buffer.as_ref();
        le_bytes::read_u16(&data[field::WALL_CLOCK_ID]).into()
    }

    /// Return the `n_clocks` field
    #[inline]
    pub fn n_clocks(&self) -> u16 {
        let data = self.buffer.as_ref();
        le_bytes::read_u16(&data[field::N_CLOCKS])
    }

    /// Return the `n_log_entries` field
    #[inline]
    pub fn n_log_entries(&self) -> u32 {
        let data = self.buffer.as_ref();
        le_bytes::read_u32(&data[field::N_LOG_ENTRIES])
    }
}

impl<'a, T: AsRef<[u8]> + ?Sized> WireReport<&'a T> {
    /// Return a pointer to the payload
    #[inline]
    pub fn payload(&self) -> &'a [u8] {
        let data = self.buffer.as_ref();
        &data[field::PAYLOAD]
    }
}

impl<T: AsRef<[u8]> + AsMut<[u8]>> WireReport<T> {
    /// Set the `fingerprint` field to
    /// [Self::FINGERPRINT](struct.WireReport.html#associatedconstant.FINGERPRINT)
    #[inline]
    pub fn set_fingerprint(&mut self) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::FINGERPRINT], Self::FINGERPRINT);
    }

    /// Set the `probe_id` field
    #[inline]
    pub fn set_probe_id(&mut self, value: ProbeId) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::PROBE_ID], value.get_raw());
    }

    /// Set the `clock` field
    #[inline]
    pub fn set_clock(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::CLOCK], value);
    }

    /// Set the `seq_num` field
    #[inline]
    pub fn set_seq_num(&mut self, value: SequenceNumber) {
        let data = self.buffer.as_mut();
        le_bytes::write_u64(&mut data[field::SEQ_NUM], value.0);
    }

    /// Set the `persistent_epoch_counting` field
    #[inline]
    pub fn set_persistent_epoch_counting(&mut self, value: bool) {
        let data = self.buffer.as_mut();
        data[field::PERSISTENT_EPOCH_COUNTING] = u8::from(value);
    }

    /// Set the raw value of the `persistent_epoch_counting` field
    #[inline]
    pub fn set_raw_persistent_epoch_counting(&mut self, value: u8) {
        let data = self.buffer.as_mut();
        data[field::PERSISTENT_EPOCH_COUNTING] = value;
    }

    /// Set the `time_resolution` field
    #[inline]
    pub fn set_time_resolution(&mut self, value: NanosecondResolution) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::TIME_RESOLUTION], value.0);
    }

    /// Set the `wall_clock_id` field
    #[inline]
    pub fn set_wall_clock_id(&mut self, value: WallClockId) {
        let data = self.buffer.as_mut();
        le_bytes::write_u16(&mut data[field::WALL_CLOCK_ID], u16::from(value));
    }

    /// Set the `n_clocks` field
    #[inline]
    pub fn set_n_clocks(&mut self, value: u16) {
        let data = self.buffer.as_mut();
        le_bytes::write_u16(&mut data[field::N_CLOCKS], value);
    }

    /// Set the `n_log_entries` field
    #[inline]
    pub fn set_n_log_entries(&mut self, value: u32) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::N_LOG_ENTRIES], value);
    }

    /// Return a mutable pointer to the payload
    #[inline]
    pub fn payload_mut(&mut self) -> &mut [u8] {
        &mut self.buffer.as_mut()[field::PAYLOAD.start..]
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for WireReport<T> {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    static MSG_BYTES: [u8; 61] = [
        // fingerprint
        0x54, 0x50, 0x52, 0x4D,
        // probe_id: 1
        0x01, 0x00, 0x00, 0x00,
        // clock: 2
        0x02, 0x00, 0x00, 0x00,
        // seq_id: 8
        0x08, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        // persistent_epoch_counting: 0
        0x00,
        // time_resolution: 255
        0xFF, 0x00, 0x00, 0x00,
        // wall_clock_id: 1
        0x01, 0x00,
        // n_clocks: 2
        0x02, 0x00,
        // n_log_entries: 3
        0x03, 0x00, 0x00, 0x00,
        // payload
        0x01, 0x00, 0x00, 0x00,
        0x02, 0x00, 0x00, 0x00,
        0x03, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00,
        0x06, 0x00, 0x00, 0x00,
        0x07, 0x00, 0x00, 0x00,
    ];

    #[rustfmt::skip]
    static PAYLOAD_BYTES: [u8; 28] = [
        // logical_clock[0]
        0x01, 0x00, 0x00, 0x00,
        0x02, 0x00, 0x00, 0x00,
        // logial_clock[1]
        0x03, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00,
        // log_entry[0]
        0x05, 0x00, 0x00, 0x00,
        // log_entry[1]
        0x06, 0x00, 0x00, 0x00,
        // log_entry[2]
        0x07, 0x00, 0x00, 0x00,
    ];

    #[test]
    fn header_len() {
        assert_eq!(WireReport::<&[u8]>::header_len(), 33);
        let n_clocks = 12;
        let n_log_items = 14;
        assert_eq!(
            WireReport::<&[u8]>::buffer_len(n_clocks, n_log_items),
            33 + (12 * mem::size_of::<LogicalClock>()) + (14 * mem::size_of::<LogEntry>())
        );
    }

    #[test]
    fn construct() {
        let mut bytes = [0xFF; 61];
        let mut r = WireReport::new_unchecked(&mut bytes[..]);
        assert_eq!(r.check_len(), Ok(()));
        r.set_fingerprint();
        r.set_probe_id(ProbeId::new(1).unwrap());
        r.set_clock(2);
        r.set_seq_num(8.into());
        r.set_persistent_epoch_counting(false);
        r.set_time_resolution(255.into());
        r.set_wall_clock_id(1.into());
        r.set_n_clocks(2);
        r.set_n_log_entries(3);
        r.payload_mut().copy_from_slice(&PAYLOAD_BYTES[..]);
        assert_eq!(r.check_fingerprint(), Ok(()));
        assert_eq!(r.check_payload_len(), Ok(()));
        assert_eq!(&r.into_inner()[..], &MSG_BYTES[..]);
    }

    #[test]
    fn deconstruct() {
        let r = WireReport::new(&MSG_BYTES[..]).unwrap();
        assert_eq!(r.fingerprint(), WireReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id().unwrap().get_raw(), 1);
        assert_eq!(r.clock(), 2);
        assert_eq!(r.seq_num(), SequenceNumber(8));
        assert_eq!(r.persistent_epoch_counting(), false);
        assert_eq!(r.time_resolution(), 255.into());
        assert_eq!(r.wall_clock_id(), 1.into());
        assert_eq!(r.n_clocks(), 2);
        assert_eq!(r.n_log_entries(), 3);
        assert_eq!(
            r.payload_len(),
            (2 * mem::size_of::<LogicalClock>()) + (3 * mem::size_of::<LogEntry>())
        );
        assert_eq!(r.payload(), &PAYLOAD_BYTES[..]);
        let n_clock_bytes = r.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let (clock_bytes, log_bytes) = r.payload().split_at(n_clock_bytes as usize);
        assert_eq!(
            clock_bytes,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00,
                0x00, 0x00
            ]
        );
        assert_eq!(
            log_bytes,
            [0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00,]
        );
    }

    #[test]
    fn round_trip() {
        let mut bytes = [0xFF; 512];

        let wire_size = {
            let mut r = WireReport::new_unchecked(&mut bytes[..]);
            assert_eq!(r.check_len(), Ok(()));
            r.set_fingerprint();
            r.set_probe_id(ProbeId::new(100).unwrap());
            r.set_clock(0xAAAA_BBBB);
            r.set_seq_num(123.into());
            r.set_persistent_epoch_counting(true);
            r.set_time_resolution(0xABAB.into());
            r.set_wall_clock_id(0xFF.into());
            r.set_n_clocks(2);
            r.set_n_log_entries(3);
            let payload_len = r.payload_len();
            (&mut r.payload_mut()[..payload_len]).copy_from_slice(&PAYLOAD_BYTES[..]);
            assert_eq!(r.check_fingerprint(), Ok(()));
            assert_eq!(r.check_payload_len(), Ok(()));
            WireReport::<&[u8]>::header_len() + payload_len
        };

        let r = WireReport::new(&bytes[..wire_size]).unwrap();
        assert_eq!(r.fingerprint(), WireReport::<&[u8]>::FINGERPRINT);
        assert_eq!(r.probe_id().unwrap().get_raw(), 100);
        assert_eq!(r.clock(), 0xAAAA_BBBB);
        assert_eq!(r.seq_num(), SequenceNumber::from(123));
        assert_eq!(r.persistent_epoch_counting(), true);
        assert_eq!(r.time_resolution(), 0xABAB.into());
        assert_eq!(r.wall_clock_id(), 0xFF.into());
        assert_eq!(r.n_clocks(), 2);
        assert_eq!(r.n_log_entries(), 3);
        assert_eq!(
            r.payload_len(),
            (2 * mem::size_of::<LogicalClock>()) + (3 * mem::size_of::<LogEntry>())
        );
        assert_eq!(r.payload(), &PAYLOAD_BYTES[..]);
    }

    #[test]
    fn invalid_fingerprint() {
        let bytes = [0xFF; 33];
        let r = WireReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ReportWireError::InvalidFingerprint);
    }

    #[test]
    fn missing_header() {
        let bytes = [0xFF; 33 - 1];
        assert_eq!(bytes.len(), WireReport::<&[u8]>::header_len() - 1);
        let r = WireReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ReportWireError::MissingHeader);
    }

    #[test]
    fn incomplete_payload() {
        let mut bytes = MSG_BYTES.clone();
        let mut r = WireReport::new(&mut bytes[..]).unwrap();
        r.set_n_clocks(2 + 1);
        r.set_n_log_entries(3 + 1);
        let bytes = r.into_inner();
        let r = WireReport::new(&bytes[..]);
        assert_eq!(r.unwrap_err(), ReportWireError::IncompletePayload);
    }

    #[test]
    fn invalid_probe_id() {
        let mut bytes = MSG_BYTES.clone();
        le_bytes::write_u32(&mut bytes[field::PROBE_ID], 0);
        let r = WireReport::new(&bytes[..]).unwrap();
        assert_eq!(r.probe_id(), Err(ReportWireError::InvalidProbeId(0)));
    }
}
