//! Bulk Modality probe log reports

use crate::compact_log::CompactLogItem;
use crate::history::DynamicHistory;
use crate::wire::{BulkReport, BulkReportWireError};
use crate::{ExtensionBytes, ProbeId, ReportError};
use core::mem::size_of;

/// Write reports all at once into a single byte slice.
pub trait BulkReporter {
    /// Conduct necessary background activities and write
    /// the recorded reporting log to a collection backend,
    /// including arbitrary extension bytes provided.
    ///
    /// Writes the probe's internal state according to the
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
    /// Writes the probe's internal state according to the
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
        let required_bytes = BulkReport::<&[u8]>::buffer_len(n_log_bytes, n_extension_bytes);
        if destination.len() < required_bytes {
            return Err(ReportError::InsufficientDestinationSize);
        }

        let mut report = BulkReport::new_unchecked(&mut destination[..]);
        report.set_fingerprint(BulkReport::<&[u8]>::FINGERPRINT);
        report.set_probe_id(self.probe_id.get_raw());
        report.set_n_log_bytes(n_log_bytes as u32); // Checked above for range
        report.set_n_extension_bytes(n_extension_bytes as u32); // Checked above for range
        let payload_bytes = report.payload_mut();

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
    pub probe_id: ProbeId,
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
            probe_id: self.probe_id,
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

/// Attempt to split a bulk report from its on-the-wire representation
/// into its constituent parts, without unbounded copying or any allocation.
///
/// Returns the source probe id, the log payload, and the extension payload bytes.
/// The log payload bytes are expected to be interepreted as little-endian `CompactLogItem`s.
/// Payload alignment is not addressed.
#[inline]
pub fn try_bulk_from_wire_bytes<'b>(
    wire_bytes: &'b [u8],
) -> Result<
    (
        ProbeId,
        impl Iterator<Item = CompactLogItem> + 'b,
        ExtensionBytes,
    ),
    ParseBulkFromWireError,
> {
    let report = BulkReport::new_checked(&wire_bytes[..])?;
    let payload_bytes = report.payload();

    let raw_probe_id = report.probe_id();
    let probe_id = ProbeId::new(raw_probe_id)
        .ok_or_else(|| ParseBulkFromWireError::InvalidProbeId(raw_probe_id))?;

    let n_log_bytes = report.n_log_bytes();
    let (log_bytes, extension_bytes) = payload_bytes.split_at(n_log_bytes as usize);
    let log_iter = log_bytes.chunks_exact(4).map(|item_bytes| {
        CompactLogItem::from_raw(u32::from_le_bytes([
            item_bytes[0],
            item_bytes[1],
            item_bytes[2],
            item_bytes[3],
        ]))
    });
    Ok((probe_id, log_iter, ExtensionBytes(extension_bytes)))
}

/// Everything that can go wrong when attempting to interpret a bulk report
/// from the wire representation
#[derive(Debug, PartialEq, Eq)]
pub enum ParseBulkFromWireError {
    /// Wire error
    /// There was an error attempting to interpret the wire representation
    Wire(BulkReportWireError),
    /// The probe id didn't follow the rules for being
    /// a valid Modality probe-specifying ProbeId
    InvalidProbeId(u32),
}

impl From<BulkReportWireError> for ParseBulkFromWireError {
    fn from(e: BulkReportWireError) -> Self {
        ParseBulkFromWireError::Wire(e)
    }
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
        fn round_trip_bulk_report(probe_id in gen_probe_id(), log in gen_compact_log(25, 257, 514), ext_bytes in proptest::collection::vec(any::<u8>(), 0..1029)) {
            // Note the max segments, max clocks-per-segment and max events-per-segment values
            // above are pulled completely from a hat and just should try to be small enough to fit
            // in our destination buffer.
            const MEGABYTE: usize = 1024*1024;
            let mut destination = vec![0u8; MEGABYTE];
            let n_report_bytes = BulkReportSourceComponents { probe_id, log: &log }.report_with_extension(&mut destination, ExtensionBytes(&ext_bytes)).unwrap();
            let (found_id, found_log_items, found_ext_bytes) = try_bulk_from_wire_bytes(&destination[..n_report_bytes]).unwrap();
            assert_eq!(found_id, probe_id);
            assert_eq!(found_ext_bytes.0, ext_bytes.as_slice());
            let found_log: Vec<CompactLogItem> = found_log_items.collect();
            assert_eq!(found_log, log);
        }
    }
}
