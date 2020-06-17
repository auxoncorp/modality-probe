use super::{
    CausalSnapshot, DistributeError, EventId, ExtensionBytes, LogicalClock, MergeError,
    ModalityProbeInstant, ProbeId, ReportError, StorageSetupError,
};
use crate::compact_log::{CompactLogItem, CompactLogVec};
use crate::report::chunked::ChunkedReportState;
use core::cmp::{max, Ordering, PartialEq};
use core::fmt::{Error as FmtError, Formatter};
use core::mem::{align_of, size_of};
use fixed_slice_vec::single::{embed, EmbedValueError, SplitUninitError};
use fixed_slice_vec::FixedSliceVec;
use rust_lcm_codec::{DecodeFingerprintError, DecodeValueError, EncodeValueError};
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

impl LogicalClock {
    /// zeros out any empty clocks (0-count) and sorts the clocks
    /// by id
    ///
    /// returns the sorted subset of the slice containing only non-empty clocks
    #[inline]
    fn normalize_clocks(clocks: &mut [LogicalClock]) -> &[LogicalClock] {
        let mut measured_self_len = 0;
        for b in clocks.iter_mut() {
            if b.count == 0 {
                b.count = 0;
            } else {
                measured_self_len += 1;
            }
        }
        clocks.sort_unstable();
        &clocks[..measured_self_len]
    }

    /// Assumes the slices are sorted and do not contain any empty clocks
    #[inline]
    fn happened_before(left: &[LogicalClock], right: &[LogicalClock]) -> bool {
        // If `left` has more non-empty members than `right`, then `left` must have at least
        // one clock with a higher count than `right`, and thus must not have happened
        // before `right`.
        if left.len() > right.len() {
            return false;
        }
        let mut had_strictly_smaller_element = false;
        for left_clock in left {
            let right_clock_count = right
                .iter()
                .find_map(|b| {
                    if b.id == left_clock.id {
                        Some(b.count)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            if left_clock.count > right_clock_count {
                return false;
            }
            if left_clock.count < right_clock_count {
                had_strictly_smaller_element = true;
            }
        }
        for right_clock in right {
            let left_clock_count = left
                .iter()
                .find_map(|b| {
                    if b.id == right_clock.id {
                        Some(b.count)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            if left_clock_count > right_clock.count {
                return false;
            }
            if left_clock_count < right_clock.count {
                had_strictly_smaller_element = true;
            }
        }

        had_strictly_smaller_element
    }
}

impl core::fmt::Debug for CausalSnapshot {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "CausalSnapshot {{ probe_id: {}, clocks: [",
            self.probe_id
        )?;
        for clock in self.clocks.iter().take(usize::from(self.clocks_len)) {
            write!(f, "{:?}, ", clock)?;
        }
        write!(f, "], clocks_len: {}", self.clocks_len)?;
        f.write_str(" }")
    }
}

/// Do a logical clock comparison, ignoring the source probe_id
impl PartialEq for CausalSnapshot {
    fn eq(&self, other: &Self) -> bool {
        let self_len = usize::from(self.clocks_len);
        let other_len = usize::from(other.clocks_len);
        if self_len != other_len {
            return false;
        }
        // TODO - actually optimize this
        // This would be a lot easier if we could be certain these were pre-sorted and pruned,
        // but since there are publicly-manipulable fields, no such promises may be found
        let mut self_clocks = self.clocks;
        let normalized_self_clocks = LogicalClock::normalize_clocks(&mut self_clocks[..self_len]);

        let mut other_clocks = other.clocks;
        let normalized_other_clocks =
            LogicalClock::normalize_clocks(&mut other_clocks[..other_len]);
        normalized_self_clocks == normalized_other_clocks
    }
}

impl PartialOrd for CausalSnapshot {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut self_clocks = self.clocks;
        let self_len = usize::from(self.clocks_len);
        let normalized_self_clocks = LogicalClock::normalize_clocks(&mut self_clocks[..self_len]);

        let mut other_clocks = other.clocks;
        let other_len = usize::from(other.clocks_len);
        let normalized_other_clocks =
            LogicalClock::normalize_clocks(&mut other_clocks[..other_len]);

        if normalized_self_clocks == normalized_other_clocks {
            return Some(Ordering::Equal);
        }
        if LogicalClock::happened_before(normalized_self_clocks, normalized_other_clocks) {
            return Some(Ordering::Less);
        }
        if LogicalClock::happened_before(normalized_other_clocks, normalized_self_clocks) {
            return Some(Ordering::Greater);
        }
        None
    }
}

pub const MIN_CLOCKS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_CLOCKS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + 3 * size_of::<u32>()
    + MIN_CLOCKS_LEN * size_of::<LogicalClock>()
    + MIN_LOG_LEN * size_of::<CompactLogItem>();

const_assert_eq!(align_of::<usize>(), align_of::<DynamicHistory>());
const_assert_eq!(4, align_of::<LogicalClock>());
const_assert_eq!(4, align_of::<CompactLogItem>());

assert_eq_size!(u64, LogicalClock);
assert_eq_align!(u32, LogicalClock);

assert_eq_size!(u32, CompactLogItem);
assert_eq_align!(u32, CompactLogItem);

const_assert_eq!(
    10 + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<CompactLogVec<'_>>()
        + size_of::<ChunkedReportState>(),
    size_of::<DynamicHistory>()
);

/// Manages the core of a probe in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and probe log items
#[derive(Debug)]
pub struct DynamicHistory<'a> {
    pub(crate) probe_id: ProbeId,
    /// The number of events seen since the current
    /// probe's logical clock last increased.
    pub(crate) event_count: u32,
    pub(crate) chunked_report_state: ChunkedReportState,
    /// Invariants:
    ///   * The first clock is always that of the local probe id
    pub(crate) clocks: FixedSliceVec<'a, LogicalClock>,
    /// Invariants:
    ///   * This log must always contain at least one item
    ///   * The first group of items in the log must always be logical clocks,
    /// starting with the local logical clock.
    pub(crate) compact_log: CompactLogVec<'a>,
}

#[derive(Debug)]
struct ClocksFullError;

impl<'a> DynamicHistory<'a> {
    #[inline]
    pub fn new_at(
        destination: &mut [u8],
        probe_id: ProbeId,
    ) -> Result<&mut DynamicHistory, StorageSetupError> {
        let remaining_bytes = destination.len();
        if remaining_bytes < MIN_HISTORY_SIZE_BYTES {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        if destination.as_ptr().is_null() {
            return Err(StorageSetupError::NullDestination);
        }
        let history = match embed(destination, |dynamic_region_slice| {
            DynamicHistory::new(dynamic_region_slice, probe_id)
        }) {
            Ok(v) => Ok(v),
            Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::Unalignable)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported)) => {
                const_assert!(size_of::<DynamicHistory>() > 0);
                panic!("Static assertions ensure that this structure is not zero sized")
            }
            Err(EmbedValueError::ConstructionError(e)) => Err(e),
        }?;
        {
            let history_ptr = history as *mut DynamicHistory as usize;
            let clocks_ptr = history.clocks.as_slice().as_ptr() as usize;
            assert!(
                 history_ptr + size_of::<DynamicHistory>() <= clocks_ptr,
                "clocks pointer {:#X} should not overlap header [{:#X}..{:#X}] bytes, but they overlapped by {} bytes",
                clocks_ptr, history_ptr, history_ptr + size_of::<DynamicHistory>(), history_ptr + size_of::<DynamicHistory>() - clocks_ptr
            );
            assert!(
                clocks_ptr as usize + history.clocks.capacity() * size_of::<LogicalClock>()
                    <= history.compact_log.as_slice().as_ptr() as usize,
                "log pointer should not overlap clock bytes"
            );
        }

        Ok(history)
    }

    #[inline]
    fn new(
        dynamic_region_slice: &'a mut [u8],
        probe_id: ProbeId,
    ) -> Result<Self, StorageSetupError> {
        let max_n_clocks = max(
            MIN_CLOCKS_LEN,
            dynamic_region_slice.len() / 8 / size_of::<LogicalClock>(),
        );
        let clocks_region_bytes = max_n_clocks * size_of::<LogicalClock>();
        if clocks_region_bytes > dynamic_region_slice.len() {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        let (clocks_region, log_region) = dynamic_region_slice.split_at_mut(clocks_region_bytes);
        let mut clocks = FixedSliceVec::from_bytes(clocks_region);
        let mut compact_log = CompactLogVec::from_bytes(log_region);
        if clocks.capacity() < MIN_CLOCKS_LEN || compact_log.capacity() < MIN_LOG_LEN {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        clocks
            .try_push(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .expect(
                "The History.clocks field should always contain a clock for this probe instance",
            );
        // This ensures that the first log segment always has a piece of logical
        // clock information.
        DynamicHistory::write_clocks_to_log(&mut compact_log, clocks.as_slice());
        Ok(DynamicHistory {
            probe_id,
            clocks,
            compact_log,
            chunked_report_state: ChunkedReportState::default(),
            event_count: 0,
        })
    }

    /// Add an item to the internal log that records this event
    /// occurred.
    ///
    /// Note: This function silently drop events if the log has
    /// overflowed or if the instance is locked for reporting.
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        if self.chunked_report_state.is_report_in_progress() {
            return;
        }
        let len = self.compact_log.len();
        let cap = self.compact_log.capacity();
        if len == cap {
            return;
        }
        // N.B. point for future improvement - basic compression here
        if self
            .compact_log
            .try_push(CompactLogItem::event(event_id))
            .is_ok()
        {
            self.event_count = self.event_count.saturating_add(1);
        }
    }

    /// Add the event and its payload to the internal log, recording
    /// that this event occurred.
    ///
    /// Note: This function silently drop events if the log has
    /// overflowed or if the instance is locked for reporting.
    #[inline]
    pub(crate) fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        if self.chunked_report_state.is_report_in_progress() {
            return;
        }
        let len = self.compact_log.len();
        let cap = self.compact_log.capacity();
        // Room for two?
        if len + 1 >= cap {
            return;
        }
        let (ev, payload) = CompactLogItem::event_with_payload(event_id, payload);
        if self.compact_log.try_push(ev).is_err() {
            return;
        }
        if self.compact_log.try_push(payload).is_ok() {
            self.event_count = self.event_count.saturating_add(1);
        }
    }

    /// Increments the clock in the logical clock corresponding to this probe instance
    #[inline]
    fn increment_local_clock_count(&mut self) {
        // N.B. We rely on the fact that the first member of the clocks
        // collection is always the clock for this probe
        debug_assert!(self.probe_id == self.clocks[0].id);
        debug_assert!(
            !self.chunked_report_state.is_report_in_progress(),
            "Should not be incrementing the local clock count when a report is in progress"
        );
        self.clocks.as_mut_slice()[0].count = self.clocks.as_slice()[0].count.saturating_add(1);
        self.event_count = 0;
    }

    /// Produce an opaque snapshot of the causal state for
    /// transmission within the system under test and include the
    /// given metadata in the snapshot's extension metadata field.
    ///
    /// If the write was successful, returns the number of bytes written.
    #[inline]
    pub(crate) fn write_lcm_snapshot_with_metadata(
        &mut self,
        destination: &mut [u8],
        meta: ExtensionBytes<'_>,
    ) -> Result<usize, DistributeError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(DistributeError::ReportLockConflict);
        }
        // Increment and log the local logical clock first, so we know that both
        // local and remote events (from probes which ingest this blob) can be
        // related to previous local events.
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();

        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::in_system::begin_causal_snapshot_write(&mut buffer_writer)?;
        let mut w = w
            .write_probe_id(self.probe_id.get_raw() as i32)?
            .write_n_clocks(self.clocks.len() as i32)?;
        for (item_writer, clock) in (&mut w).zip(self.clocks.as_slice()) {
            item_writer.write(|bw| {
                Ok(bw
                    .write_probe_id(clock.id.get_raw() as i32)?
                    .write_count(clock.count as i32)?)
            })?
        }
        let w = w.done()?;
        let w = w.write_n_extension_bytes(meta.0.len() as i32)?;
        let _w: lcm::in_system::causal_snapshot_write_done<_> =
            w.extension_bytes_copy_from_slice(meta.0)?;
        Ok(buffer_writer.cursor())
    }

    /// Produce a transparent but limited snapshot of the causal state for transmission
    /// within the system under test
    #[inline]
    pub(crate) fn write_fixed_size_snapshot(&mut self) -> Result<CausalSnapshot, DistributeError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(DistributeError::ReportLockConflict);
        }
        let mut clocks = [LogicalClock {
            id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
            count: 0,
        }; 256];
        if self.clocks.len() > clocks.len() {
            return Err(DistributeError::InsufficientDestinationSize);
        }
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        let mut non_empty_clocks_count: usize = 0;
        for (source, sink) in self
            .clocks
            .as_slice()
            .iter()
            .filter(|b| b.count > 0)
            .zip(clocks.iter_mut())
        {
            sink.id = source.id;
            sink.count = source.count;
            non_empty_clocks_count += 1;
        }

        Ok(CausalSnapshot {
            probe_id: self.probe_id.get_raw(),
            clocks,
            clocks_len: non_empty_clocks_count as u8,
        })
    }
    #[inline]
    pub(crate) fn merge_from_lcm_snapshot_bytes<'d>(
        &'_ mut self,
        source: &'d [u8],
    ) -> Result<ExtensionBytes<'d>, MergeError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(MergeError::ReportLockConflict);
        }
        impl From<DecodeValueError<rust_lcm_codec::BufferReaderError>> for MergeError {
            #[inline]
            fn from(_: DecodeValueError<rust_lcm_codec::BufferReaderError>) -> Self {
                MergeError::ExternalHistoryEncoding
            }
        }
        impl From<DecodeFingerprintError<rust_lcm_codec::BufferReaderError>> for MergeError {
            #[inline]
            fn from(_: DecodeFingerprintError<rust_lcm_codec::BufferReaderError>) -> Self {
                MergeError::ExternalHistoryEncoding
            }
        }
        let mut buffer_reader = rust_lcm_codec::BufferReader::new(source);
        let r = lcm::in_system::begin_causal_snapshot_read(&mut buffer_reader)?;
        let (neighbor_id, r) = r.read_probe_id()?;
        let (_n_clock_clocks, mut r) = r.read_n_clocks()?;
        let clocks_iterator = (&mut r).map(|item_reader| {
            let mut found_id = 0;
            let mut found_count = 0;
            let item_read_result = item_reader.read(|ir| {
                let (id, ir) = ir.read_probe_id()?;
                found_id = id;
                let (count, ir) = ir.read_count()?;
                found_count = count;
                Ok(ir)
            });
            if item_read_result.is_err() {
                Err(MergeError::ExternalHistoryEncoding)
            } else {
                match ProbeId::new(found_id as u32) {
                    Some(id) => Ok(LogicalClock {
                        id,
                        count: found_count as u32,
                    }),
                    None => Err(MergeError::ExternalHistorySemantics),
                }
            }
        });
        let merge_result = self.merge_internal(neighbor_id as u32, clocks_iterator);
        // Confirm we have fully read the causal snapshot message
        let r = r.done()?;
        let (n_extension_bytes, r) = r.read_n_extension_bytes()?;
        let (_extension_bytes, _r): (_, lcm::in_system::causal_snapshot_read_done<_>) =
            r.extension_bytes_as_slice()?;
        // Here we rely on the fact that the extension bytes are the last thing in the message to
        // drag them out of the original source buffer.
        // N.B. If the schema ever changes such that there are more contents after the
        // extension bytes, this technique will cease to work.
        let extension_bytes_end_index = buffer_reader.cursor();
        let extension_bytes = &source
            [extension_bytes_end_index - (n_extension_bytes as usize)..extension_bytes_end_index];
        debug_assert_eq!(extension_bytes.len(), n_extension_bytes as usize);
        merge_result.map(|_| ExtensionBytes(extension_bytes))
    }

    /// Merge a publicly-transmittable causal history into our specialized local in-memory storage
    #[inline]
    pub(crate) fn merge_fixed_size(
        &mut self,
        external_history: &CausalSnapshot,
    ) -> Result<(), MergeError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(MergeError::ReportLockConflict);
        }
        let num_incoming_clocks = usize::from(external_history.clocks_len);
        self.merge_internal(
            external_history.probe_id,
            external_history
                .clocks
                .iter()
                .take(num_incoming_clocks)
                .map(|b| Ok(*b)),
        )
    }

    #[inline]
    fn merge_internal<B>(
        &mut self,
        raw_neighbor_id: u32,
        clocks_iterator: B,
    ) -> Result<(), MergeError>
    where
        B: Iterator<Item = Result<LogicalClock, MergeError>>,
    {
        let external_id = match ProbeId::new(raw_neighbor_id) {
            Some(id) => id,
            None => return Err(MergeError::ExternalHistorySemantics),
        };
        // Ensure that there is a clock for the neighbor that sent the snapshot
        if !self.clocks.as_slice().iter().any(|b| b.id == external_id)
            && self
                .clocks
                .try_push(LogicalClock {
                    id: external_id,
                    count: 0,
                })
                .is_err()
        {
            let _ = self
                .compact_log
                .try_push(CompactLogItem::event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED));
            return Err(MergeError::ExceededAvailableClocks);
        }

        let mut outcome = Ok(());
        for external_clock in clocks_iterator {
            let external_clock = match external_clock {
                Ok(b) => b,
                Err(e) => {
                    outcome = Err(e);
                    break;
                }
            };
            if external_clock.count == 0 {
                continue;
            }
            for internal_clock in self.clocks.as_mut_slice() {
                // N.B This depends on the local clock already having been created, above,
                // when we received a history from the clock's source probe_id.
                // During early probe event recording, may cause us to drop
                // data from an indirect neighbor that
                // is also a direct neighbor (but has not yet sent us a message).
                if internal_clock.id == external_clock.id {
                    internal_clock.count = max(internal_clock.count, external_clock.count);
                    break;
                }
            }
        }
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        outcome
    }

    #[inline]
    fn write_clocks_to_log<'d>(compact_log: &mut CompactLogVec<'d>, clocks: &[LogicalClock]) {
        if compact_log.is_full() {
            return;
        }
        let max_len_that_can_fit_a_clock_and_overflow_notice =
            (compact_log.capacity() - 2) as usize;
        let mut log_len = compact_log.len();
        let mut has_overflowed_log = false;
        for b in clocks {
            let (id, count) = CompactLogItem::clock(*b);
            if log_len < max_len_that_can_fit_a_clock_and_overflow_notice {
                compact_log
                    .try_push(id)
                    .expect("Already checked id will fit");
                compact_log
                    .try_push(count)
                    .expect("Already checked count will fit");
                log_len += 2;
            } else {
                // TODO - instead of breaking in the middle, should we have just not written
                // any of the logical clock at all?
                has_overflowed_log = true;
                break;
            }
        }
        if has_overflowed_log {
            let _ = compact_log.try_push(CompactLogItem::event(EventId::EVENT_LOG_OVERFLOWED));
        }
    }

    #[inline]
    fn write_current_clocks_to_log(&mut self) {
        let clocks = self.clocks.as_slice();
        let log = &mut self.compact_log;
        DynamicHistory::write_clocks_to_log(log, clocks);
    }

    pub(crate) fn finished_report_logging(&mut self) {
        self.compact_log.clear();
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);
    }

    pub(crate) fn now(&self) -> ModalityProbeInstant {
        ModalityProbeInstant {
            clock: self.clocks[0],
            event_count: self.event_count,
        }
    }
}

impl From<EncodeValueError<rust_lcm_codec::BufferWriterError>> for DistributeError {
    #[inline]
    fn from(e: EncodeValueError<rust_lcm_codec::BufferWriterError>) -> Self {
        match e {
            EncodeValueError::ArrayLengthMismatch(_) => DistributeError::Encoding,
            EncodeValueError::InvalidValue(_) => DistributeError::Encoding,
            EncodeValueError::WriterError(_) => DistributeError::InsufficientDestinationSize,
        }
    }
}
impl From<rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>>
    for DistributeError
{
    #[inline]
    fn from(_: rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>) -> Self {
        DistributeError::InsufficientDestinationSize
    }
}

impl From<EncodeValueError<rust_lcm_codec::BufferWriterError>> for ReportError {
    #[inline]
    fn from(e: EncodeValueError<rust_lcm_codec::BufferWriterError>) -> Self {
        match e {
            EncodeValueError::ArrayLengthMismatch(_) => ReportError::Encoding,
            EncodeValueError::InvalidValue(_) => ReportError::Encoding,
            EncodeValueError::WriterError(_) => ReportError::InsufficientDestinationSize,
        }
    }
}
impl From<rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>>
    for ReportError
{
    #[inline]
    fn from(_: rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>) -> Self {
        ReportError::InsufficientDestinationSize
    }
}

#[allow(dead_code)]
mod lcm {
    include!(concat!(env!("OUT_DIR"), "/in_system.rs"));
}
