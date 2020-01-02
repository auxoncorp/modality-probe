use super::{CausalSnapshot, EventId, LocalStorageCreationError, LogicalClockBucket, TracerId};
use core::cmp::{max, Ordering, PartialEq};
use core::fmt::{Error as FmtError, Formatter};
use core::mem::{align_of, size_of};
use core::num::NonZeroU32;
use static_assertions::{assert_eq_align, assert_eq_size, const_assert_eq};

impl LogicalClockBucket {
    /// zeros out any empty buckets (0-id or 0-count) and sorts the buckets
    /// by id
    ///
    /// returns the sorted subset of the slice containing only non-empty buckets
    #[inline]
    fn normalize_buckets(buckets: &mut [LogicalClockBucket]) -> &[LogicalClockBucket] {
        let mut measured_self_len = 0;
        for b in buckets.iter_mut() {
            if b.id == 0 || b.count == 0 {
                b.count = 0;
                b.id = 0;
            } else {
                measured_self_len += 1;
            }
        }
        buckets.sort_unstable();
        &buckets[..measured_self_len]
    }

    /// Assumes the slices are sorted and do not contain any empty buckets
    #[inline]
    fn happened_before(left: &[LogicalClockBucket], right: &[LogicalClockBucket]) -> bool {
        // If `left` has more non-empty members than `right`, then `left` must have at least
        // one bucket with a higher count than `right`, and thus must not have happened
        // before `right`.
        if left.len() > right.len() {
            return false;
        }
        let mut had_strictly_smaller_element = false;
        for left_bucket in left {
            let right_bucket_count = right
                .iter()
                .find_map(|b| {
                    if b.id == left_bucket.id {
                        Some(b.count)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            if left_bucket.count > right_bucket_count {
                return false;
            }
            if left_bucket.count < right_bucket_count {
                had_strictly_smaller_element = true;
            }
        }
        for right_bucket in right {
            let left_bucket_count = left
                .iter()
                .find_map(|b| {
                    if b.id == right_bucket.id {
                        Some(b.count)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            if left_bucket_count > right_bucket.count {
                return false;
            }
            if left_bucket_count < right_bucket.count {
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
            "CausalSnapshot {{ tracer_id: {}, buckets: [",
            self.tracer_id
        )?;
        for bucket in self.buckets.iter().take(usize::from(self.buckets_len)) {
            write!(f, "{:?}, ", bucket)?;
        }
        write!(f, "], buckets_len: {}", self.buckets_len)?;
        f.write_str(" }")
    }
}

/// Do a logical clock comparison, ignoring the source tracer_id
impl PartialEq for CausalSnapshot {
    fn eq(&self, other: &Self) -> bool {
        let self_len = usize::from(self.buckets_len);
        let other_len = usize::from(other.buckets_len);
        if self_len != other_len {
            return false;
        }
        // TODO - actually optimize this
        // This would be a lot easier if we could be certain these were pre-sorted and pruned,
        // but since there are publicly-manipulable fields, no such promises may be found
        let mut self_buckets = self.buckets;
        let normalized_self_buckets =
            LogicalClockBucket::normalize_buckets(&mut self_buckets[..self_len]);

        let mut other_buckets = other.buckets;
        let normalized_other_buckets =
            LogicalClockBucket::normalize_buckets(&mut other_buckets[..other_len]);
        normalized_self_buckets == normalized_other_buckets
    }
}

impl PartialOrd for CausalSnapshot {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut self_buckets = self.buckets;
        let self_len = usize::from(self.buckets_len);
        let normalized_self_buckets =
            LogicalClockBucket::normalize_buckets(&mut self_buckets[..self_len]);

        let mut other_buckets = other.buckets;
        let other_len = usize::from(other.buckets_len);
        let normalized_other_buckets =
            LogicalClockBucket::normalize_buckets(&mut other_buckets[..other_len]);

        if normalized_self_buckets == normalized_other_buckets {
            return Some(Ordering::Equal);
        }
        if LogicalClockBucket::happened_before(normalized_self_buckets, normalized_other_buckets) {
            return Some(Ordering::Less);
        }
        if LogicalClockBucket::happened_before(normalized_other_buckets, normalized_self_buckets) {
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
    max_buckets_len: u32,

    /// How many log items (individual events *AND* logical clock flushes)
    ///
    /// Each time we record a local event
    /// Each time the logical clock flushes, it should add up to 2 * max_buckets log items
    ///
    /// Should always be greater than 1
    max_log_len: u32,
}

pub const MIN_BUCKETS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_BUCKETS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + size_of::<u32>()
    + MIN_BUCKETS_LEN * size_of::<LogicalClockBucket>()
    + MIN_LOG_LEN * size_of::<CompactLogItem>();

const_assert_eq!(8, align_of::<DynamicHistory>());
const_assert_eq!(4, align_of::<LogicalClockBucket>());
const_assert_eq!(4, align_of::<CompactLogItem>());
const_assert_eq!(4, align_of::<u32>());

const_assert_eq!(8, align_of::<u64>());

assert_eq_size!(u64, LogicalClockBucket);
assert_eq_align!(u32, LogicalClockBucket);

assert_eq_size!(u32, CompactLogItem);
assert_eq_align!(u32, CompactLogItem);

const_assert_eq!(16 + 4 * size_of::<usize>(), size_of::<DynamicHistory>());

/// Fixed-size portion of the dynamic history
#[derive(Debug)]
#[repr(C)]
pub struct DynamicHistory {
    tracer_id: u32,
    config: DynamicHistoryConfig,
    has_overflowed_log: bool,
    has_overflowed_num_buckets: bool,

    buckets_len: usize,
    buckets: *mut LogicalClockBucket,

    log_len: usize,
    log_pointer: *mut CompactLogItem,
}

#[derive(Debug)]
struct BucketsFullError;

/// In a stream of these:
///     if the first bit is not set, treat it as recording an Event
///     if the first bit is set, treat the rest of the value as a TracerId for a LogicalClockBucket
///         AND the next item in the stream should be interpreted as a count for that bucket.
#[repr(transparent)]
pub struct CompactLogItem(u32);

impl CompactLogItem {
    fn event(event_id: EventId) -> Self {
        // The construction checks for EventId should prevent the top bit from being set
        CompactLogItem(event_id.get_raw())
    }
    #[must_use]
    fn bucket(bucket: LogicalClockBucket) -> (Self, Self) {
        // Set the top bit for id to indicate that it is not an event but a logical clock bucket,
        // and to treat the next item as the count. Don't separate these two!
        let id = bucket.id | 0b1000_0000_0000_0000;
        (CompactLogItem(id), CompactLogItem(bucket.count))
    }
}

impl DynamicHistory {
    pub fn new_at(
        destination: &mut [u8],
        tracer_id: TracerId,
    ) -> Result<&mut DynamicHistory, LocalStorageCreationError> {
        let remaining_bytes = destination.len();
        if remaining_bytes < MIN_HISTORY_SIZE_BYTES {
            return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
        }
        if destination.as_ptr().is_null() {
            return Err(LocalStorageCreationError::NullDestination);
        }

        let (header_ptr, header_bytes) = {
            let header_align_offset = destination
                .as_mut_ptr()
                .align_offset(align_of::<DynamicHistory>());
            let header_bytes = header_align_offset + size_of::<DynamicHistory>();
            if header_bytes > remaining_bytes {
                return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
            }
            let header_ptr =
                unsafe { destination.as_mut_ptr().add(header_align_offset) as *mut DynamicHistory };
            if header_ptr.is_null() {
                return Err(LocalStorageCreationError::NullDestination);
            }
            (header_ptr, header_bytes)
        };
        let remaining_bytes = remaining_bytes - header_bytes;
        let dynamic_region_ptr = unsafe { destination.as_mut_ptr().add(header_bytes) };

        let (buckets_ptr, buckets_bytes, max_buckets_len) = {
            // Try to give 1/8 of our remaining space to the buckets
            let buckets_align_offset =
                dynamic_region_ptr.align_offset(align_of::<LogicalClockBucket>());
            if buckets_align_offset > remaining_bytes {
                return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
            }
            let max_buckets_len = max(
                MIN_BUCKETS_LEN,
                (remaining_bytes - buckets_align_offset) / 8 / size_of::<LogicalClockBucket>(),
            );
            let buckets_bytes =
                buckets_align_offset + max_buckets_len * size_of::<LogicalClockBucket>();
            if buckets_bytes > remaining_bytes {
                return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
            }
            (
                unsafe { dynamic_region_ptr.add(buckets_align_offset) as *mut LogicalClockBucket },
                buckets_bytes,
                max_buckets_len,
            )
        };
        assert!(
            header_ptr as usize + header_bytes <= buckets_ptr as usize,
            "buckets pointer should not overlap header bytes"
        );

        let dynamic_region_ptr = unsafe { dynamic_region_ptr.add(buckets_bytes) };
        let remaining_bytes = remaining_bytes - buckets_bytes;

        let log_align_offset = dynamic_region_ptr.align_offset(align_of::<CompactLogItem>());
        let remaining_bytes = remaining_bytes
            .checked_sub(log_align_offset)
            .ok_or_else(|| LocalStorageCreationError::UnderMinimumAllowedSize)?;
        let max_log_len = remaining_bytes / size_of::<CompactLogItem>();
        if max_log_len < MIN_LOG_LEN {
            return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
        }
        let log_ptr = unsafe { dynamic_region_ptr.add(log_align_offset) as *mut CompactLogItem };

        if max_buckets_len > core::u32::MAX as usize || max_log_len > core::u32::MAX as usize {
            return Err(LocalStorageCreationError::ExceededMaximumAddressableSize);
        }
        assert!(
            buckets_ptr as usize + buckets_bytes <= log_ptr as usize,
            "log pointer should not overlap bucket bytes"
        );

        let mut history_header = DynamicHistory {
            tracer_id: tracer_id.get_raw(),
            config: DynamicHistoryConfig {
                max_buckets_len: max_buckets_len as u32,
                max_log_len: max_log_len as u32,
            },
            has_overflowed_log: false,
            has_overflowed_num_buckets: false,
            buckets_len: 0,
            buckets: buckets_ptr,
            log_len: 0,
            log_pointer: log_ptr,
        };
        history_header
            .try_push_bucket(LogicalClockBucket {
                id: tracer_id.get_raw(),
                count: 0,
            })
            .expect(
                "The History.buckets field should always contain a bucket for this tracer instance",
            );
        unsafe {
            *header_ptr = history_header;
            let header_ref = header_ptr.as_mut().expect(
                "We already checked to be sure header_ptr was not null, and yet it is now null",
            );
            Ok(header_ref)
        }
    }

    fn try_push_bucket(&mut self, bucket: LogicalClockBucket) -> Result<(), BucketsFullError> {
        if self.buckets_len < self.config.max_buckets_len as usize {
            unsafe {
                *self.buckets.add(self.buckets_len) = bucket;
            }
            self.buckets_len += 1;
            Ok(())
        } else {
            Err(BucketsFullError)
        }
    }

    fn get_buckets_slice(&self) -> &[LogicalClockBucket] {
        unsafe {
            core::slice::from_raw_parts(self.buckets as *const LogicalClockBucket, self.buckets_len)
        }
    }

    fn get_buckets_slice_mut(&mut self) -> &mut [LogicalClockBucket] {
        unsafe {
            core::slice::from_raw_parts_mut(
                self.buckets as *mut LogicalClockBucket,
                self.buckets_len,
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

    /// Increments the bucket in the logical clock corresponding to this tracer instance
    fn increment_local_bucket_count(&mut self) {
        // N.B. We rely on the fact that the first member of the buckets
        // collection is always the bucket for this tracer
        unsafe {
            (*self.buckets).count = (*self.buckets).count.saturating_add(1);
        }
    }

    /// Produce an opaque snapshot of the causal state for transmission
    /// within the system under test
    ///
    /// If the write was successful, returns the number of bytes written
    pub(crate) fn write_lcm_logical_clock(&mut self, destination: &mut [u8]) -> Result<usize, ()> {
        self.increment_local_bucket_count();
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        // TODO - more error piping? Right now we assume remediation is largely infeasible.
        // TODO - all this borrowing of Copy-type primitives for writes is an anti-pattern,
        // need to fix in codegen
        let w = lcm::in_system::Causal_snapshot::begin_write(&mut buffer_writer).map_err(|_| ())?;
        let mut w = w
            .write_tracer_id(&(self.tracer_id as i64))
            .map_err(|_| ())?
            .write_n_clock_buckets(&(self.buckets_len as i32))
            .map_err(|_| ())?;
        for (i, item_writer) in (&mut w).enumerate() {
            let bucket: &mut LogicalClockBucket = unsafe { &mut *self.buckets.add(i) };
            item_writer
                .write(|bw| {
                    Ok(bw
                        .write_tracer_id(&(bucket.id as i32))?
                        .write_count(&(bucket.count as i32))?)
                })
                .map_err(|_| ())?
        }
        let _w = w.done().map_err(|_| ())?;
        Ok(buffer_writer.cursor())
    }

    /// Produce a transparent but limited snapshot of the causal state for transmission
    /// within the system under test
    pub(crate) fn fixed_size_snapshot(&mut self) -> CausalSnapshot {
        self.increment_local_bucket_count();
        let mut buckets = arr_macro::arr![LogicalClockBucket { id: 0, count: 0}; 256];
        let mut non_empty_buckets_count: usize = 0;
        for (source, sink) in self
            .get_buckets_slice()
            .iter()
            .filter(|b| b.count > 0)
            .zip(buckets.iter_mut())
        {
            sink.id = source.id;
            sink.count = source.count;
            non_empty_buckets_count += 1;
        }

        CausalSnapshot {
            tracer_id: self.tracer_id,
            buckets,
            buckets_len: non_empty_buckets_count as u8,
        }
    }
    pub(crate) fn merge_from_bytes(&mut self, source: &[u8]) -> Result<(), ()> {
        // TODO - interpret as LCM and merge
        let neighbor_id = unimplemented!();
        let buckets_iterator = core::iter::empty();
        self.merge_internal(neighbor_id, buckets_iterator)
    }

    /// Merge a publicly-transmittable causal history into our specialized local in-memory storage
    pub(crate) fn merge_fixed_size(&mut self, external_history: &CausalSnapshot) -> Result<(), ()> {
        let num_incoming_buckets = usize::from(external_history.buckets_len);
        self.merge_internal(
            external_history.tracer_id,
            external_history.buckets.iter().take(num_incoming_buckets),
        )
    }

    fn merge_internal<'a, B>(
        &'a mut self,
        raw_neighbor_id: u32,
        buckets_iterator: B,
    ) -> Result<(), ()>
    where
        B: Iterator<Item = &'a LogicalClockBucket>,
    {
        let external_id = match TracerId::new(raw_neighbor_id) {
            Some(id) => id,
            // Invalid external id, can't trust anything it says
            None => return Err(()),
        };
        let raw_neighbor_id = external_id.get_raw();
        // Ensure that there is a bucket for the neighbor that sent the snapshot
        if !self
            .get_buckets_slice()
            .iter()
            .any(|b| b.id == raw_neighbor_id)
        {
            if self
                .try_push_bucket(LogicalClockBucket {
                    id: raw_neighbor_id,
                    count: 0,
                })
                .is_err()
            {
                self.has_overflowed_num_buckets = true;
            }
        }

        for external_bucket in buckets_iterator.filter(|b| b.count != 0) {
            let id = match NonZeroU32::new(external_bucket.id) {
                Some(id) => TracerId(id),
                // Can't add this bucket to the state if we don't have a valid id for it
                None => continue,
            };
            let raw_id = id.get_raw();
            for internal_bucket in self.get_buckets_slice_mut() {
                // N.B This depends on the local bucket bucket already having been created, above,
                // when we received a history from the bucket's source tracer_id.
                // During early tracing, may cause us to drop data from an indirect neighbor that
                // is also a direct neighbor (but has not yet sent us a message).
                if internal_bucket.id == raw_id {
                    internal_bucket.count = max(internal_bucket.count, external_bucket.count);
                    break;
                }
            }
        }
        self.increment_local_bucket_count();
        self.write_current_buckets_to_log();
        if self.has_overflowed_num_buckets {
            Err(())
        } else {
            Ok(())
        }
    }

    fn write_current_buckets_to_log(&mut self) {
        if self.has_overflowed_log {
            return;
        }
        let max_len_that_can_fit_a_bucket = (self.config.max_log_len - 1) as usize;
        let mut log_len = self.log_len;
        let mut has_overflowed_log = false;
        for b in self.get_buckets_slice() {
            let (id, count) = CompactLogItem::bucket(*b);
            if log_len < max_len_that_can_fit_a_bucket {
                unsafe {
                    *self.log_pointer.add(self.log_len) = id;
                    *self.log_pointer.add(self.log_len + 1) = count;
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

    /// Send the log to the backend, containing:
    ///   * The local tracer id
    ///   * Error flags
    ///   * Event ids for events that have happened since the last backend send
    ///   * Interspersed snapshots of the logical clock
    pub(crate) fn send_to_backend(&mut self, backend: &mut dyn super::Backend) {
        // TODO - proper LCM serialization of all the docs-mentioned content
        // TODO - do we need to reserve space in our dynamically allocated memory for use
        // in writing our LCM message out?
        let snapshot = self.fixed_size_snapshot();
        let snapshot_slice: &[u8] = unsafe {
            core::slice::from_raw_parts(
                (&snapshot as *const CausalSnapshot) as *const u8,
                core::mem::size_of::<CausalSnapshot>(),
            )
        };
        let send_succeeded = backend.send_tracer_data(snapshot_slice);
        if send_succeeded {
            self.clear_log();
            self.record_event(super::BACKEND_SEND_SUCCESSFUL_EVENT);
            self.write_current_buckets_to_log();
            // TODO - Should we use some other mechanism for recording/identifying this internal event?
        }
    }
}

mod lcm {
    include!(concat!(env!("OUT_DIR"), "/in_system.rs"));
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}
