//! Provides a wire format for a "report" from a probe. A report is a
//! section of the probe's event log prepended by the most up-to-date
//! neighbor clocks UP TO that report.
use core::mem;

use crate::{log::LogEntry, wire::le_bytes, LogicalClock, ProbeId};

/// A read/write wrapper around a bulk report buffer
#[derive(Debug, Clone)]
pub struct WireReport<T: AsRef<[u8]>> {
    buffer: T,
}

/// Everything that can go wrong when attempting to interpret a bulk
/// report from the wire representation
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
// TODO(dan@auxon.io): derive error
pub enum WireReportError {
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

mod field {
    type Field = ::core::ops::Range<usize>;
    type Rest = ::core::ops::RangeFrom<usize>;

    /// A magical (constant) value used as a hint about the data
    /// encoded in this pile of bytes.
    pub const FINGERPRINT: Field = 0..4;
    /// A u32 representing the probe_id of the Modality probe instance
    /// producing this report.
    pub const PROBE_ID: Field = 4..8;
    /// The packed clock value for the probe at the time that this
    /// report was created.
    pub const CLOCK: Field = 8..12;
    /// The sequence number of the report within a single clock value,
    /// used to order reports created between clock ticks.
    pub const SEQ_NUM: Field = 12..14;
    /// The number of frontier clocks present in the payload.
    ///
    /// Note: These are at the front of the payload and are specially
    /// encoded as frontier clocks.
    pub const N_CLOCKS: Field = 14..16;
    /// The number of log entries present in the payload.
    pub const N_LOG_ENTRIES: Field = 16..20;
    pub const PAYLOAD: Rest = 20..;
}

impl<T: AsRef<[u8]>> WireReport<T> {
    /// Report fingerprint (MRPT)
    pub const FINGERPRINT: u32 = 0x4D_52_50_54;
    /// The length of the wire header.
    pub const HEADER_LEN: usize = field::PAYLOAD.start;

    /// Make a new `WireReport` and confirm its fingerprint and
    /// length.
    pub fn new(buf: T) -> Result<Self, WireReportError> {
        let report = WireReport::init_from(buf);
        report.check_fingerprint()?;
        report.verify_len()?;
        Ok(report)
    }

    // TODO(dan@auxon.io): new_unchecked
    /// Construct a `WireReport` around the given buffer, ready to be
    /// filled with header, clocks, and log entries.
    pub fn init_from(buffer: T) -> Self {
        WireReport { buffer }
    }

    /// Check for the expected fingerprint value.
    ///
    /// Returns `Err(WireReportError::InvalidFingerprint)` if the fingerprint
    /// does not match.
    pub fn check_fingerprint(&self) -> Result<(), WireReportError> {
        if self.fingerprint() != Self::FINGERPRINT {
            Err(WireReportError::InvalidFingerprint)
        } else {
            Ok(())
        }
    }

    /// Consumes the bulk report, returning the underlying buffer
    pub fn into_inner(self) -> T {
        self.buffer
    }

    /// Return the `fingerprint` field
    #[inline]
    pub fn fingerprint(&self) -> u32 {
        let data = self.buffer.as_ref();
        le_bytes::read_u32(&data[field::FINGERPRINT])
    }

    /// Return the `clock` field
    #[inline]
    pub fn clock(&self) -> u32 {
        let data = self.buffer.as_ref();
        le_bytes::read_u32(&data[field::CLOCK])
    }

    /// Return the `seq_num` field
    #[inline]
    pub fn seq_num(&self) -> u16 {
        let data = self.buffer.as_ref();
        le_bytes::read_u16(&data[field::SEQ_NUM])
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

    /// Return the `probe_id` field
    #[inline]
    pub fn probe_id(&self) -> Result<ProbeId, WireReportError> {
        let data = self.buffer.as_ref();
        let raw_probe_id = le_bytes::read_u32(&data[field::PROBE_ID]);
        match ProbeId::new(raw_probe_id) {
            Some(id) => Ok(id),
            None => Err(WireReportError::InvalidProbeId(raw_probe_id)),
        }
    }

    /// Verify that the length of the buffer jives with the data in
    /// the header
    #[inline]
    pub fn verify_len(&self) -> Result<(), WireReportError> {
        let clocks_bytes = self.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let entries_bytes = self.n_log_entries() as usize * mem::size_of::<LogEntry>();
        if self.buffer.as_ref().len() != clocks_bytes + entries_bytes + Self::HEADER_LEN {
            // TODO(dan@auxon.io): This is probably not the right error.
            return Err(WireReportError::IncompletePayload);
        }
        Ok(())
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
    /// [Self::FINGERPRINT](struct.Report.html#associatedconstant.FINGERPRINT)
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
    pub fn set_seq_num(&mut self, value: u16) {
        let data = self.buffer.as_mut();
        le_bytes::write_u16(&mut data[field::SEQ_NUM], value);
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

    /// Return the payload section of the report as a mutable
    /// slice. It's used to copy data into a report.
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
