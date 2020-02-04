use super::{
    CausalSnapshot, DistributeError, EkotraceNow, EventId, ExtensionBytes, LogicalClock,
    MergeError, ReportError, StorageSetupError, TracerId,
};
use crate::compact_log::{self, CompactLogItem, CompactLogVec};
use core::cmp::{max, Ordering, PartialEq};
use core::convert::TryInto;
use core::fmt::{Error as FmtError, Formatter};
use core::mem::{align_of, size_of};
use rust_lcm_codec::{DecodeFingerprintError, DecodeValueError, EncodeValueError};
use slice_vec::slice_single::{embed, EmbedValueError, SplitUninitError};
use slice_vec::SliceVec;
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

impl LogicalClock {
    /// zeros out any empty clocks (0-id or 0-count) and sorts the clocks
    /// by id
    ///
    /// returns the sorted subset of the slice containing only non-empty clocks
    #[inline]
    fn normalize_clocks(clocks: &mut [LogicalClock]) -> &[LogicalClock] {
        let mut measured_self_len = 0;
        for b in clocks.iter_mut() {
            if b.id == 0 || b.count == 0 {
                b.count = 0;
                b.id = 0;
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
            "CausalSnapshot {{ tracer_id: {}, clocks: [",
            self.tracer_id
        )?;
        for clock in self.clocks.iter().take(usize::from(self.clocks_len)) {
            write!(f, "{:?}, ", clock)?;
        }
        write!(f, "], clocks_len: {}", self.clocks_len)?;
        f.write_str(" }")
    }
}

/// Do a logical clock comparison, ignoring the source tracer_id
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
    8 + size_of::<SliceVec<'_, LogicalClock>>() + size_of::<CompactLogVec<'_>>(),
    size_of::<DynamicHistory>()
);

/// Manages the core of a tracer in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and tracing log items
#[derive(Debug)]
#[repr(C)]
pub struct DynamicHistory<'a> {
    tracer_id: u32,
    report_event_index: u32,

    clocks: SliceVec<'a, LogicalClock>,
    compact_log: CompactLogVec<'a>,
}

#[derive(Debug)]
struct ClocksFullError;

impl<'a> DynamicHistory<'a> {
    #[inline]
    pub fn new_at(
        destination: &mut [u8],
        tracer_id: TracerId,
    ) -> Result<&mut DynamicHistory, StorageSetupError> {
        let remaining_bytes = destination.len();
        if remaining_bytes < MIN_HISTORY_SIZE_BYTES {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        if destination.as_ptr().is_null() {
            return Err(StorageSetupError::NullDestination);
        }
        let history = match embed(destination, |dynamic_region_slice| {
            let max_n_clocks = max(
                MIN_CLOCKS_LEN,
                dynamic_region_slice.len() / 8 / size_of::<LogicalClock>(),
            );
            let clocks_region_bytes = max_n_clocks * size_of::<LogicalClock>();
            if clocks_region_bytes > dynamic_region_slice.len() {
                return Err(StorageSetupError::UnderMinimumAllowedSize);
            }
            let (clocks_region, log_region) =
                dynamic_region_slice.split_at_mut(clocks_region_bytes);
            let clocks = SliceVec::from_bytes(clocks_region);
            let compact_log = CompactLogVec::from_bytes(log_region);
            if clocks.capacity() < MIN_CLOCKS_LEN || compact_log.capacity() < MIN_LOG_LEN {
                return Err(StorageSetupError::UnderMinimumAllowedSize);
            }
            Ok(DynamicHistory {
                tracer_id: tracer_id.get_raw(),
                clocks,
                compact_log,
                report_event_index: 0,
            })
        }) {
            Ok(v) => Ok(v),
            Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
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

        history
            .clocks
            .try_push(LogicalClock {
                id: tracer_id.get_raw(),
                count: 0,
            })
            .expect(
                "The History.clocks field should always contain a clock for this tracer instance",
            );

        // This ensures that the first log segment always has a piece of logical
        // clock information.
        history.write_current_clocks_to_log();

        Ok(history)
    }

    #[inline]
    fn clear_log(&mut self) {
        self.compact_log.clear();
        self.report_event_index = 0;
    }

    /// Add an item to the internal log that records this event occurred
    ///
    /// May silently drop events if the log has overflowed
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        let len = self.compact_log.len();
        let cap = self.compact_log.capacity();
        if len == cap {
            return;
        }
        if len == cap - 1 {
            let _ = self
                .compact_log
                .try_push(CompactLogItem::event(EventId::EVENT_LOG_OVERFLOWED));
            return;
        }
        // N.B. point for future improvement - basic compression here
        if self
            .compact_log
            .try_push(CompactLogItem::event(event_id))
            .is_ok()
        {
            self.report_event_index += 1;
        }
    }

    /// Increments the clock in the logical clock corresponding to this tracer instance
    #[inline]
    fn increment_local_clock_count(&mut self) {
        // N.B. We rely on the fact that the first member of the clocks
        // collection is always the clock for this tracer
        self.clocks.as_mut_slice()[0].count = self.clocks.as_slice()[0].count.saturating_add(1);
    }

    /// Produce an opaque snapshot of the causal state for
    /// transmission within the system under test and include the
    /// given metadata in the snapshot's extension metadata field.
    ///
    /// If the write was successful, returns the number of bytes written.
    #[inline]
    pub(crate) fn write_lcm_logical_clock_with_metadata(
        &mut self,
        destination: &mut [u8],
        meta: ExtensionBytes<'_>,
    ) -> Result<usize, DistributeError> {
        // Increment and log the local logical clock first, so we know that both
        // local and remote events (from tracers which ingest this blob) can be
        // related to previous local events.
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();

        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::in_system::begin_causal_snapshot_write(&mut buffer_writer)?;
        let mut w = w
            .write_tracer_id(self.tracer_id as i32)?
            .write_n_clocks(self.clocks.len() as i32)?;
        for (item_writer, clock) in (&mut w).zip(self.clocks.as_slice()) {
            item_writer.write(|bw| {
                Ok(bw
                    .write_tracer_id(clock.id as i32)?
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
    pub(crate) fn write_fixed_size_logical_clock(
        &mut self,
    ) -> Result<CausalSnapshot, DistributeError> {
        let mut clocks = [LogicalClock { id: 0, count: 0 }; 256];
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
            tracer_id: self.tracer_id,
            clocks,
            clocks_len: non_empty_clocks_count as u8,
        })
    }
    #[inline]
    pub(crate) fn merge_from_lcm_log_report_bytes<'d>(
        &'_ mut self,
        source: &'d [u8],
    ) -> Result<ExtensionBytes<'d>, MergeError> {
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
        let (neighbor_id, r) = r.read_tracer_id()?;
        let (_n_clock_clocks, mut r) = r.read_n_clocks()?;
        let clocks_iterator = (&mut r).map(|item_reader| {
            let mut found_id = 0;
            let mut found_count = 0;
            let item_read_result = item_reader.read(|ir| {
                let (id, ir) = ir.read_tracer_id()?;
                found_id = id;
                let (count, ir) = ir.read_count()?;
                found_count = count;
                Ok(ir)
            });
            if item_read_result.is_err() {
                Err(MergeError::ExternalHistoryEncoding)
            } else {
                Ok(LogicalClock {
                    id: found_id as u32,
                    count: found_count as u32,
                })
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
        let num_incoming_clocks = usize::from(external_history.clocks_len);
        self.merge_internal(
            external_history.tracer_id,
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
        let external_id = match TracerId::new(raw_neighbor_id) {
            Some(id) => id,
            None => return Err(MergeError::ExternalHistorySemantics),
        };
        let raw_neighbor_id = external_id.get_raw();
        // Ensure that there is a clock for the neighbor that sent the snapshot
        if !self
            .clocks
            .as_slice()
            .iter()
            .any(|b| b.id == raw_neighbor_id)
            && self
                .clocks
                .try_push(LogicalClock {
                    id: raw_neighbor_id,
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
            let id: TracerId = match external_clock.id.try_into() {
                Ok(id) => id,
                // Can't add this clock to the state if we don't have a valid id for it
                Err(_) => {
                    outcome = Err(MergeError::ExternalHistorySemantics);
                    break;
                }
            };
            let raw_id = id.get_raw();
            for internal_clock in self.clocks.as_mut_slice() {
                // N.B This depends on the local clock already having been created, above,
                // when we received a history from the clock's source tracer_id.
                // During early tracing, may cause us to drop data from an indirect neighbor that
                // is also a direct neighbor (but has not yet sent us a message).
                if internal_clock.id == raw_id {
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
    fn write_current_clocks_to_log(&mut self) {
        if self.compact_log.is_full() {
            return;
        }
        let max_len_that_can_fit_a_clock_and_overflow_notice =
            (self.compact_log.capacity() - 2) as usize;
        let mut log_len = self.compact_log.len();
        let mut has_overflowed_log = false;
        for b in self.clocks.as_slice() {
            let (id, count) = CompactLogItem::clock(*b);
            if log_len < max_len_that_can_fit_a_clock_and_overflow_notice {
                self.compact_log
                    .try_push(id)
                    .expect("Already checked id will fit");
                self.compact_log
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
            let _ = self
                .compact_log
                .try_push(CompactLogItem::event(EventId::EVENT_LOG_OVERFLOWED));
        }
    }

    /// Produce a report for external use, containing:
    ///   * The local tracer id
    ///   * Error flags
    ///   * Event ids for events that have happened since the last backend send
    ///   * Interspersed snapshots of the logical clock
    #[inline]
    pub(crate) fn write_lcm_log_report(
        &mut self,
        destination: &mut [u8],
        extension: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::log_reporting::begin_log_report_write(&mut buffer_writer)?;
        let w = w.write_tracer_id(self.tracer_id as i32)?;
        let mut log_items = self.compact_log.as_slice();
        let expected_n_segments = compact_log::count_segments(log_items);
        let mut w = w.write_n_segments(expected_n_segments as i32)?;
        let mut actually_written_segments = 0;
        let mut actually_written_log_items = 0;
        for segment_item_writer in &mut w {
            let segment = compact_log::split_next_segment(log_items);
            log_items = segment.rest;
            segment_item_writer.write(|sw| {
                let sw = sw.write_n_clocks(segment.clock_region.len() as i32 / 2)?;
                let mut sw = sw.write_n_events(segment.event_region.len() as i32)?;
                for (clock_item_writer, clock_parts) in
                    (&mut sw).zip(segment.clock_region.chunks_exact(2))
                {
                    clock_item_writer.write(|bw| {
                        let tracer_id = clock_parts[0].interpret_as_logical_clock_tracer_id();
                        Ok(bw
                            .write_tracer_id(tracer_id as i32)?
                            .write_count(clock_parts[1].raw() as i32)?)
                    })?;
                }
                actually_written_log_items += segment.clock_region.len();
                let mut sw = sw.done()?;
                for (event_item_writer, event) in (&mut sw).zip(segment.event_region) {
                    event_item_writer.write(event.raw() as i32)?;
                }
                actually_written_log_items += segment.event_region.len();
                Ok(sw.done()?)
            })?;
            actually_written_segments += 1;
        }
        assert_eq!(
            expected_n_segments, actually_written_segments,
            "number of written segments should match the amount we tried"
        );
        assert_eq!(
            actually_written_log_items,
            self.compact_log.len(),
            "we should have written all of the log items into the segments"
        );
        let w = w.done()?;
        let w = w.write_n_extension_bytes(extension.0.len() as i32)?;
        let _w: lcm::log_reporting::log_report_write_done<_> =
            w.extension_bytes_copy_from_slice(extension.0)?;

        self.clear_log();
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);
        Ok(buffer_writer.cursor())
    }

    pub(crate) fn now(&self) -> EkotraceNow {
        EkotraceNow {
            logical_clock: self.clocks[0],
            report_event_index: self.report_event_index,
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
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}
