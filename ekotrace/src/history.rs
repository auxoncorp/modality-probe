use super::{
    CausalSnapshot, DistributeError, EventId, LogicalClock, MergeError, ReportError,
    StorageSetupError, TracerId,
};
use crate::compact_log::{self, CompactLogItem};
use core::cmp::{max, Ordering, PartialEq};
use core::convert::TryInto;
use core::fmt::{Error as FmtError, Formatter};
use core::mem::{align_of, size_of};
use rust_lcm_codec::{DecodeFingerprintError, DecodeValueError, EncodeValueError};
use static_assertions::{assert_eq_align, assert_eq_size, const_assert_eq};

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

#[derive(Debug)]
#[repr(C)]
struct DynamicHistoryConfig {
    /// Corresponds to the maximum number of neighbors that are
    /// expected to send messages to this tracer, plus this instance
    ///
    /// Should always be greater than 1
    max_clocks_len: u32,

    /// How many log items (individual events *AND* logical clock flushes)
    ///
    /// Each time we record a local event
    /// Each time the logical clock flushes, it should add up to 2 * max_clocks log items
    ///
    /// Should always be greater than 1
    max_log_len: u32,
}

pub const MIN_BUCKETS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_BUCKETS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + size_of::<u32>()
    + MIN_BUCKETS_LEN * size_of::<LogicalClock>()
    + MIN_LOG_LEN * size_of::<CompactLogItem>();

const_assert_eq!(align_of::<usize>(), align_of::<DynamicHistory>());
const_assert_eq!(4, align_of::<LogicalClock>());
const_assert_eq!(4, align_of::<CompactLogItem>());

assert_eq_size!(u64, LogicalClock);
assert_eq_align!(u32, LogicalClock);

assert_eq_size!(u32, CompactLogItem);
assert_eq_align!(u32, CompactLogItem);

const_assert_eq!(16 + 4 * size_of::<usize>(), size_of::<DynamicHistory>());

/// Manages the core of a tracer in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and tracing log items
#[derive(Debug)]
#[repr(C)]
pub struct DynamicHistory {
    tracer_id: u32,
    config: DynamicHistoryConfig,
    has_overflowed_log: bool,
    has_overflowed_num_clocks: bool,

    /// How many clocks are populated
    clocks_len: usize,
    /// Pointer to the array of current
    /// logical clock values
    clocks: *mut LogicalClock,

    /// How many log entries are populated
    log_len: usize,
    /// Pointer to the array of log items
    log_pointer: *mut CompactLogItem,
}

#[derive(Debug)]
struct ClocksFullError;

impl DynamicHistory {
    #[allow(clippy::cast_ptr_alignment)]
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
        let (header_ptr, header_bytes) = {
            let header_align_offset = destination
                .as_mut_ptr()
                .align_offset(align_of::<DynamicHistory>());
            let header_bytes = header_align_offset + size_of::<DynamicHistory>();
            if header_bytes > remaining_bytes {
                return Err(StorageSetupError::UnderMinimumAllowedSize);
            }
            let header_ptr =
                unsafe { destination.as_mut_ptr().add(header_align_offset) as *mut DynamicHistory };
            if header_ptr.is_null() {
                return Err(StorageSetupError::NullDestination);
            }
            (header_ptr, header_bytes)
        };
        let remaining_bytes = remaining_bytes - header_bytes;
        let dynamic_region_ptr = unsafe { destination.as_mut_ptr().add(header_bytes) };

        let (clocks_ptr, clocks_bytes, max_clocks_len) = {
            // Try to give 1/8 of our remaining space to the clocks
            let clocks_align_offset = dynamic_region_ptr.align_offset(align_of::<LogicalClock>());
            if clocks_align_offset > remaining_bytes {
                return Err(StorageSetupError::UnderMinimumAllowedSize);
            }
            let max_clocks_len = max(
                MIN_BUCKETS_LEN,
                (remaining_bytes - clocks_align_offset) / 8 / size_of::<LogicalClock>(),
            );
            let clocks_bytes = clocks_align_offset + max_clocks_len * size_of::<LogicalClock>();
            if clocks_bytes > remaining_bytes {
                return Err(StorageSetupError::UnderMinimumAllowedSize);
            }
            let clocks_ptr =
                unsafe { dynamic_region_ptr.add(clocks_align_offset) as *mut LogicalClock };
            assert!(
                header_ptr as usize + size_of::<DynamicHistory>() <= clocks_ptr as usize,
                "clocks pointer {:#X} should not overlap header [{:#X}..{:#X}] bytes, but they overlapped by {} bytes",
                clocks_ptr as usize, header_ptr as usize, header_ptr as usize + header_bytes, (header_ptr as usize + header_bytes - clocks_ptr as usize)
            );
            (clocks_ptr, clocks_bytes, max_clocks_len)
        };

        let dynamic_region_ptr = unsafe { dynamic_region_ptr.add(clocks_bytes) };
        let remaining_bytes = remaining_bytes - clocks_bytes;

        let log_align_offset = dynamic_region_ptr.align_offset(align_of::<CompactLogItem>());
        let remaining_bytes = remaining_bytes
            .checked_sub(log_align_offset)
            .ok_or_else(|| StorageSetupError::UnderMinimumAllowedSize)?;
        let max_log_len = remaining_bytes / size_of::<CompactLogItem>();
        if max_log_len < MIN_LOG_LEN {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        let log_ptr = unsafe { dynamic_region_ptr.add(log_align_offset) as *mut CompactLogItem };

        if max_clocks_len > core::u32::MAX as usize || max_log_len > core::u32::MAX as usize {
            return Err(StorageSetupError::ExceededMaximumAddressableSize);
        }
        assert!(
            clocks_ptr as usize + clocks_bytes <= log_ptr as usize,
            "log pointer should not overlap clock bytes"
        );

        let mut history_header = DynamicHistory {
            tracer_id: tracer_id.get_raw(),
            config: DynamicHistoryConfig {
                max_clocks_len: max_clocks_len as u32,
                max_log_len: max_log_len as u32,
            },
            has_overflowed_log: false,
            has_overflowed_num_clocks: false,
            clocks_len: 0,
            clocks: clocks_ptr,
            log_len: 0,
            log_pointer: log_ptr,
        };
        history_header
            .try_push_clock(LogicalClock {
                id: tracer_id.get_raw(),
                count: 0,
            })
            .expect(
                "The History.clocks field should always contain a clock for this tracer instance",
            );

        // This ensures that the first log segment always has a piece of logical
        // clock information.
        history_header.write_current_clocks_to_log();

        unsafe {
            *header_ptr = history_header;
            let header_ref = header_ptr.as_mut().expect(
                "We already checked to be sure header_ptr was not null, and yet it is now null",
            );
            Ok(header_ref)
        }
    }

    fn try_push_clock(&mut self, clock: LogicalClock) -> Result<(), ClocksFullError> {
        if self.clocks_len < self.config.max_clocks_len as usize {
            unsafe {
                *self.clocks.add(self.clocks_len) = clock;
            }
            self.clocks_len += 1;
            Ok(())
        } else {
            Err(ClocksFullError)
        }
    }

    fn get_clocks_slice(&self) -> &[LogicalClock] {
        unsafe { core::slice::from_raw_parts(self.clocks as *const LogicalClock, self.clocks_len) }
    }

    fn get_clocks_slice_mut(&mut self) -> &mut [LogicalClock] {
        unsafe {
            core::slice::from_raw_parts_mut(self.clocks as *mut LogicalClock, self.clocks_len)
        }
    }

    fn get_log_slice(&self) -> &[CompactLogItem] {
        unsafe {
            core::slice::from_raw_parts(
                self.log_pointer as *mut CompactLogItem as *const CompactLogItem,
                self.log_len,
            )
        }
    }

    fn clear_log(&mut self) {
        self.log_len = 0;
        self.has_overflowed_log = false;
    }

    /// Add an item to the internal log that records this event occurred
    ///
    /// May silently drop events if the log has overflowed
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        if self.has_overflowed_log {
            return;
        }
        // N.B. point for future improvement - basic compression here
        if self.log_len < self.config.max_log_len as usize {
            unsafe {
                *self.log_pointer.add(self.log_len) = CompactLogItem::event(event_id);
            }
            self.log_len += 1;
        } else {
            self.has_overflowed_log = true;
        }
    }

    /// Increments the clock in the logical clock corresponding to this tracer instance
    fn increment_local_clock_count(&mut self) {
        // N.B. We rely on the fact that the first member of the clocks
        // collection is always the clock for this tracer
        unsafe {
            (*self.clocks).count = (*self.clocks).count.saturating_add(1);
        }
    }

    /// Produce an opaque snapshot of the causal state for transmission
    /// within the system under test.
    ///
    /// If the write was successful, returns the number of bytes written.
    pub(crate) fn write_lcm_logical_clock(
        &mut self,
        destination: &mut [u8],
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
            .write_n_clocks(self.clocks_len as i32)?;
        for (i, item_writer) in (&mut w).enumerate() {
            let clock: &mut LogicalClock = unsafe { &mut *self.clocks.add(i) };
            item_writer.write(|bw| {
                Ok(bw
                    .write_tracer_id(clock.id as i32)?
                    .write_count(clock.count as i32)?)
            })?
        }
        let w = w.done()?;
        let w = w.write_n_extension_bytes(0)?;
        let _w: lcm::in_system::causal_snapshot_write_done<_> = w.done()?;
        Ok(buffer_writer.cursor())
    }

    /// Produce a transparent but limited snapshot of the causal state for transmission
    /// within the system under test
    pub(crate) fn write_fixed_size_logical_clock(
        &mut self,
    ) -> Result<CausalSnapshot, DistributeError> {
        let mut clocks = [LogicalClock { id: 0, count: 0 }; 256];
        if self.clocks_len > clocks.len() {
            return Err(DistributeError::InsufficientDestinationSize);
        }
        self.increment_local_clock_count();
        let mut non_empty_clocks_count: usize = 0;
        for (source, sink) in self
            .get_clocks_slice()
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
    pub(crate) fn merge_from_lcm_log_report_bytes(
        &mut self,
        source: &[u8],
    ) -> Result<(), MergeError> {
        impl From<DecodeValueError<rust_lcm_codec::BufferReaderError>> for MergeError {
            fn from(_: DecodeValueError<rust_lcm_codec::BufferReaderError>) -> Self {
                MergeError::ExternalHistoryEncoding
            }
        }
        impl From<DecodeFingerprintError<rust_lcm_codec::BufferReaderError>> for MergeError {
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
        let (_n_extension_bytes, mut r) = r.read_n_extension_bytes()?;
        // N.B. Expect to replace this iteration with cheaper slice-based skip-ahead
        // when rust-lcm-codegen is updated to provide special case options for byte arrays.
        for extension_bytes_item_reader in &mut r {
            let _extension_byte = extension_bytes_item_reader.read()?;
        }
        let _read_done_result: lcm::in_system::causal_snapshot_read_done<_> = r.done()?;
        merge_result
    }

    /// Merge a publicly-transmittable causal history into our specialized local in-memory storage
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
            .get_clocks_slice()
            .iter()
            .any(|b| b.id == raw_neighbor_id)
            && self
                .try_push_clock(LogicalClock {
                    id: raw_neighbor_id,
                    count: 0,
                })
                .is_err()
        {
            self.has_overflowed_num_clocks = true;
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
            for internal_clock in self.get_clocks_slice_mut() {
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

    fn write_current_clocks_to_log(&mut self) {
        if self.has_overflowed_log {
            return;
        }
        let max_len_that_can_fit_a_clock = (self.config.max_log_len - 1) as usize;
        let mut log_len = self.log_len;
        let mut has_overflowed_log = false;
        for b in self.get_clocks_slice() {
            let (id, count) = CompactLogItem::clock(*b);
            if log_len < max_len_that_can_fit_a_clock {
                unsafe {
                    *self.log_pointer.add(log_len) = id;
                    *self.log_pointer.add(log_len + 1) = count;
                }
                log_len += 2;
            } else {
                // TODO - instead of breaking in the middle, should we have just not written
                // any of the logical clock at all?
                has_overflowed_log = true;
                break;
            }
        }
        self.log_len = log_len;
        self.has_overflowed_log |= has_overflowed_log;
    }

    /// Produce a report for external use, containing:
    ///   * The local tracer id
    ///   * Error flags
    ///   * Event ids for events that have happened since the last backend send
    ///   * Interspersed snapshots of the logical clock
    pub(crate) fn write_lcm_log_report(
        &mut self,
        destination: &mut [u8],
    ) -> Result<usize, ReportError> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::log_reporting::begin_log_report_write(&mut buffer_writer)?;
        let w = w.write_tracer_id(self.tracer_id as i32)?;
        let w = w.write_flags(|fw| {
            let fw = fw.write_has_overflowed_log(self.has_overflowed_log)?;
            let fw = fw.write_has_overflowed_num_clocks(self.has_overflowed_num_clocks)?;
            Ok(fw)
        })?;

        let mut log_items = self.get_log_slice();
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
            actually_written_log_items, self.log_len,
            "we should have written all of the log items into the segments"
        );
        let w = w.done()?;
        let w = w.write_n_extension_bytes(0)?;
        let _w: lcm::log_reporting::log_report_write_done<_> = w.done()?;

        self.clear_log();
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);
        Ok(buffer_writer.cursor())
    }
}

impl From<EncodeValueError<rust_lcm_codec::BufferWriterError>> for DistributeError {
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
    fn from(_: rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>) -> Self {
        DistributeError::InsufficientDestinationSize
    }
}

impl From<EncodeValueError<rust_lcm_codec::BufferWriterError>> for ReportError {
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
    fn from(_: rust_lcm_codec::EncodeFingerprintError<rust_lcm_codec::BufferWriterError>) -> Self {
        ReportError::InsufficientDestinationSize
    }
}

#[allow(dead_code)]
mod lcm {
    include!(concat!(env!("OUT_DIR"), "/in_system.rs"));
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}
