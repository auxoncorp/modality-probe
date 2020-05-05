//! A wire protocol for representing ekotrace log reports
//! that are fragmented into multiple chunks due to sizing
//! constraints
//!
use crate::compact_log::CompactLogItem;
use crate::history::DynamicHistory;
use crate::{ExtensionBytes, ReportError, TracerId};
use core::mem::{align_of, size_of};
use static_assertions::{assert_eq_align, const_assert_eq};

/// Write reports all at once into a single byte slice.
pub trait BulkReporter {
    /// Conduct necessary background activities and write
    /// the recorded reporting log to a collection backend,
    /// including arbitrary extension bytes provided.
    ///
    /// Writes the Tracer's internal state according to the
    /// log reporting schema.
    ///
    /// If the write was successful, returns the number of *bytes* written
    fn report_with_extension(
        &mut self,
        destination: &mut [u8],
        extension_metadata: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError>;

    /// Conduct necessary background activities and write
    /// the recorded reporting log to a collection backend.
    ///
    /// Writes the Tracer's internal state according to the
    /// bulk log reporting format.
    ///
    /// If the write was successful, returns the number of *bytes* written
    fn report(&mut self, destination: &mut [u8]) -> Result<usize, ReportError> {
        self.report_with_extension(destination, ExtensionBytes(&[]))
    }
}
impl<'log> BulkReporter for BulkReportSourceComponents<'log> {
    fn report_with_extension(
        &mut self,
        destination: &mut [u8],
        extension_metadata: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError> {
        let n_log_bytes = self.log.len() * size_of::<CompactLogItem>();
        let n_extension_bytes = extension_metadata.0.len();
        if n_log_bytes > core::u32::MAX as usize {
            // We don't currently support sending reports with logs that big.
            // N.B. Point for future improvement - actually only send some of the log
            // by doing some pre-segmentation and determining where we can cut it up,
            // possibly injecting duplicate clocks as necessary.
            return Err(ReportError::Encoding);
        }
        if n_extension_bytes > core::u32::MAX as usize {
            // We don't support sending reports with extensions that big.
            // There likely isn't a valid remediation available
            // since the extension data is opaque.
            return Err(ReportError::Extension);
        }
        let required_bytes = size_of::<WireBulkHeader>() + n_log_bytes + n_extension_bytes;
        if destination.len() < required_bytes {
            return Err(ReportError::InsufficientDestinationSize);
        }
        // We consider this relatively safe because WireBulkHeader is a largely
        // uninterpreted pile of bytes fields all with alignments == 1
        // and we know from the above check that there's enough size
        assert_eq_align!(u8, WireBulkHeader);
        let (header_bytes, payload_bytes) = destination.split_at_mut(size_of::<WireBulkHeader>());
        let header = unsafe { &mut *(header_bytes.as_mut_ptr() as *mut WireBulkHeader) };
        header.fingerprint = bulk_framing_fingerprint();
        header.location_id = self.location_id.get_raw().to_le_bytes();
        header.n_log_bytes = (n_log_bytes as u32).to_le_bytes(); // Checked above for range
        header.n_extension_bytes = (n_extension_bytes as u32).to_le_bytes(); // Checked above for range

        let (log_bytes, extension_bytes) = payload_bytes.split_at_mut(n_log_bytes);
        if super::write_log_as_little_endian_bytes(log_bytes, self.log).is_err() {
            return Err(ReportError::InsufficientDestinationSize);
        }
        extension_bytes[..n_extension_bytes].copy_from_slice(extension_metadata.0);
        Ok(required_bytes)
    }
}

/// The parts necessary to take an in-memory
/// representation of a causal log and produce
/// a bulk report wire representation.
///
/// Note that this is *not* the on-the-wire
/// representation, but rather an intermediate
/// helper that can be used to make said data.
pub struct BulkReportSourceComponents<'log> {
    /// Where the log data was created/about
    pub location_id: TracerId,
    /// The compact log of events and clocks
    pub log: &'log [CompactLogItem],
}

impl<'data> BulkReporter for DynamicHistory<'data> {
    #[inline]
    fn report_with_extension(
        &mut self,
        destination: &mut [u8],
        extension_metadata: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(ReportError::ReportLockConflict);
        }
        let log = self.compact_log.as_slice();
        let r = BulkReportSourceComponents {
            location_id: self.tracer_id,
            log,
        }
        .report_with_extension(destination, extension_metadata);
        match r {
            Ok(v) => {
                self.finished_report_logging();
                Ok(v)
            }
            Err(e) => Err(e),
        }
    }
}

/// Fixed-sized always-initialized header portion of the bulk report format
#[repr(C, align(1))]
pub struct WireBulkHeader {
    /// A magical (constant) value used as a hint about the
    /// data encoded in this pile of bytes.
    pub fingerprint: [u8; 4],
    /// A u32 representing the tracer_id (a.k.a. location id) of the
    /// ekotrace agent instance producing this report.
    pub location_id: [u8; 4],
    /// How many of the payload bytes are populated with log data?
    pub n_log_bytes: [u8; 4],
    /// How many of the payload bytes are populated with extension data?
    pub n_extension_bytes: [u8; 4],
}
const_assert_eq!(1, align_of::<WireBulkHeader>());
const_assert_eq!(16, size_of::<WireBulkHeader>());

/// Attempt to split a bulk report from its on-the-wire representation
/// into its constituent parts, without unbounded copying or any allocation.
///
/// Returns the source location id, the log payload bytes, and the extension payload bytes.
/// The log payload bytes are expected to be interepreted as little-endian `CompactLogItem`s.
/// Payload alignment is not addressed.
pub fn try_bulk_from_wire_bytes(
    wire_bytes: &[u8],
) -> Result<(TracerId, &[u8], ExtensionBytes), ParseBulkFromWireError> {
    if wire_bytes.len() < size_of::<WireBulkHeader>() {
        return Err(ParseBulkFromWireError::MissingHeader);
    }
    assert_eq_align!(u8, WireBulkHeader);
    debug_assert_eq!(
        0,
        wire_bytes.as_ptr() as usize % align_of::<WireBulkHeader>()
    );
    let (header_bytes, payload_bytes) = wire_bytes.split_at(size_of::<WireBulkHeader>());
    let wire_header = unsafe { &*(header_bytes.as_ptr() as *const WireBulkHeader) };
    if wire_header.fingerprint != bulk_framing_fingerprint() {
        return Err(ParseBulkFromWireError::InvalidFingerprint);
    }
    let raw_location_id = u32::from_le_bytes(wire_header.location_id);
    let location_id = TracerId::new(raw_location_id)
        .ok_or_else(|| ParseBulkFromWireError::InvalidTracerId(raw_location_id))?;
    let n_log_bytes = u32::from_le_bytes(wire_header.n_log_bytes);
    let n_extension_bytes = u32::from_le_bytes(wire_header.n_extension_bytes);

    if payload_bytes.len() < n_log_bytes as usize {
        return Err(ParseBulkFromWireError::IncompletePayload);
    }
    let (log_bytes, extension_bytes) = payload_bytes.split_at(n_log_bytes as usize);
    if extension_bytes.len() < n_extension_bytes as usize {
        return Err(ParseBulkFromWireError::IncompletePayload);
    }
    Ok((location_id, log_bytes, ExtensionBytes(extension_bytes)))
}

/// Everything that can go wrong when attempting to interpret a bulk report
/// from the wire representation
#[derive(Debug, PartialEq, Eq)]
pub enum ParseBulkFromWireError {
    /// The fingerprint didn't match expectations
    InvalidFingerprint,
    /// There weren't enough bytes for a full header
    MissingHeader,
    /// There weren't enough payload bytes (based on
    /// expectations from inspecting the header).
    IncompletePayload,
    /// The tracer id didn't follow the rules for being
    /// a valid ekotrace-location-specifying TracerId
    InvalidTracerId(u32),
}

const BULK_FRAMING_FINGERPRINT_SOURCE: u32 = 0x45_42_4C_4B; // EBLK
/// Little endian representation of the chunk format's chunk message
/// fingerprint.
pub fn bulk_framing_fingerprint() -> [u8; 4] {
    BULK_FRAMING_FINGERPRINT_SOURCE.to_le_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compact_log::log_tests::*;
    use crate::id::id_tests::*;
    use proptest::prelude::*;
    use proptest::std_facade::*;

    proptest! {
        #[test]
        fn round_trip_bulk_report(location_id in gen_tracer_id(), log in gen_compact_log(25, 257, 514), ext_bytes in proptest::collection::vec(any::<u8>(), 0..1029)) {
            // Note the max segments, max clocks-per-segment and max events-per-segment values
            // above are pulled completely from a hat and just should try to be small enough to fit
            // in our destination buffer.
            const MEGABYTE: usize = 1024*1024;
            let mut destination = vec![0u8; MEGABYTE];
            let n_report_bytes = BulkReportSourceComponents { location_id, log: &log }.report_with_extension(&mut destination, ExtensionBytes(&ext_bytes)).unwrap();
            let (found_id, found_log_bytes, found_ext_bytes) = try_bulk_from_wire_bytes(&destination[..n_report_bytes]).unwrap();
            assert_eq!(found_id, location_id);
            assert_eq!(found_ext_bytes.0, ext_bytes.as_slice());
            let mut found_log = Vec::new();
            assert_eq!(0, found_log_bytes.len() % 4);
            for item_bytes in found_log_bytes.chunks_exact(4) {
                found_log.push(CompactLogItem::from_raw(u32::from_le_bytes([
                    item_bytes[0],
                    item_bytes[1],
                    item_bytes[2],
                    item_bytes[3],
                ])));
            }
            assert_eq!(found_log, log);
        }
    }
}
