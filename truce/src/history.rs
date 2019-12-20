use super::{CausalSnapshot, EventId, LogicalClockBucket, TracerId};
use crate::MERGE_INBAND_CAUSALITY_EVENT;
use arrayvec::ArrayVec;
use core::cmp::{max, Ordering, PartialEq};
use core::fmt::{Error as FmtError, Formatter};
use core::num::NonZeroU32;

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

/// In-memory structure for tracer data storage
#[derive(Debug, PartialEq, PartialOrd)]
pub(crate) struct History {
    tracer_id: TracerId,
    /// Collection of ids which represent this instance and its immediate neighbors
    in_the_neighborhood: ArrayVec<[TracerId; 32]>,
    has_overflowed_neighborhood: bool,

    local_bucket_index: usize,
    buckets: ArrayVec<[Bucket; 256]>,

    event_log: ArrayVec<[(EventId, u16); 512]>,
    has_overflowed_event_log: bool,
    has_overflowed_num_buckets: bool,
}

/// Implementation internal in-memory storage of logical clock bucket
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Bucket {
    id: TracerId,
    count: u32,
}

impl History {
    pub(crate) fn new(tracer_id: TracerId) -> Self {
        let mut in_the_neighborhood = ArrayVec::new();
        in_the_neighborhood.push(tracer_id);
        let mut buckets = ArrayVec::new();
        buckets.push(Bucket {
            id: tracer_id,
            count: 0,
        });
        History {
            tracer_id,
            in_the_neighborhood,
            has_overflowed_neighborhood: false,
            local_bucket_index: 0,
            buckets,
            event_log: ArrayVec::new(),
            has_overflowed_event_log: false,
            has_overflowed_num_buckets: false,
        }
    }

    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        let my_bucket = unsafe { self.buckets.get_unchecked_mut(self.local_bucket_index) };
        my_bucket.count = my_bucket.count.saturating_add(1);
        let needs_new_entry = if let Some(last_event) = self.event_log.last_mut() {
            if last_event.0 == event_id {
                if last_event.1 == core::u16::MAX {
                    true
                } else {
                    last_event.1 += 1;
                    false
                }
            } else {
                true
            }
        } else {
            true
        };
        if needs_new_entry && self.event_log.try_push((event_id, 1)).is_err() {
            self.has_overflowed_event_log = true;
        }
    }

    /// Produce a snapshot of the causal state
    pub(crate) fn snapshot(&mut self) -> CausalSnapshot {
        let mut buckets = arr_macro::arr![LogicalClockBucket { id: 0, count: 0}; 256];
        // N.B. If we increase the size of the buckets storage, this cast may become invalid
        let mut non_empty_buckets_count: u8 = 0;
        for (source, sink) in self
            .buckets
            .iter()
            .filter(|b| b.count > 0)
            .zip(buckets.iter_mut())
        {
            sink.id = source.id.0.get();
            sink.count = source.count;
            non_empty_buckets_count += 1;
        }

        CausalSnapshot {
            tracer_id: self.tracer_id.0.get(),
            buckets,
            buckets_len: non_empty_buckets_count,
        }
    }

    /// Merge a publicly-transmittable causal history into our specialized local in-memory storage
    pub(crate) fn merge(&mut self, external_history: &CausalSnapshot) {
        let external_id = match NonZeroU32::new(external_history.tracer_id) {
            Some(id) => TracerId(id),
            // Invalid external id, can't trust anything it says
            None => return,
        };
        if !self.in_the_neighborhood.contains(&external_id)
            && self.in_the_neighborhood.try_push(external_id).is_err()
        {
            self.has_overflowed_neighborhood = true;
        }
        let num_incoming_buckets = usize::from(external_history.buckets_len);
        for external_bucket in external_history
            .buckets
            .iter()
            .take(num_incoming_buckets)
            .filter(|b| b.count != 0)
        {
            let id = match NonZeroU32::new(external_bucket.id) {
                Some(id) => TracerId(id),
                // Can't add this bucket to the state if we don't have a valid id for it
                None => continue,
            };
            // N.B During early tracing, may cause us to drop data from an indirect neighbor that
            // is also a direct neighbor (but has not yet sent us a message).
            if !self.in_the_neighborhood.contains(&id) {
                continue;
            }
            let mut found_matching_bucket = false;
            for internal_bucket in self.buckets.iter_mut() {
                if internal_bucket.id == id {
                    internal_bucket.count = max(internal_bucket.count, external_bucket.count);
                    found_matching_bucket = true;
                    break;
                }
            }

            if !found_matching_bucket
                && self
                    .buckets
                    .try_push(Bucket {
                        id,
                        count: external_bucket.count,
                    })
                    .is_err()
            {
                self.has_overflowed_num_buckets = true;
            }
        }
        self.buckets.as_mut().sort_unstable_by_key(|b| b.id);
        self.local_bucket_index = self
            .buckets
            .iter()
            .position(|b| b.id == self.tracer_id)
            .expect(
                "The History.buckets field should always contain a bucket for this tracer instance",
            );

        self.record_event(MERGE_INBAND_CAUSALITY_EVENT)
    }

    pub(crate) fn send_to_backend(&mut self, backend: &mut dyn super::Backend) {
        let snapshot = self.snapshot();
        // TODO - proper serialization per the selected format
        // TODO - incorporate event log and error flags, not just causal snapshot.
        let snapshot_slice: &[u8] = unsafe {
            core::slice::from_raw_parts(
                (&snapshot as *const CausalSnapshot) as *const u8,
                core::mem::size_of::<CausalSnapshot>(),
            )
        };
        let send_succeeded = backend.send_tracer_data(snapshot_slice);
        if send_succeeded {
            self.event_log.clear();
            // TODO - Should we use some other mechanism for recording/identifying this internal event?
            self.record_event(super::BACKEND_SEND_SUCCESSFUL_EVENT);
        }
    }
}
