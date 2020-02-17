use super::{EventId, LogicalClock, TracerId};
use fixed_slice_vec::FixedSliceVec;

const CLOCK_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
const EVENT_WITH_META_MASK: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;

pub(crate) type CompactLogVec<'a> = FixedSliceVec<'a, CompactLogItem>;

/// In a stream of these:
/// * If first bit is not set AND the second bit is not set, this is a
///   plain event id.
///
/// * If the first bit is set AND the second bit is not set, treat the
///   rest of the value as a TracerId for a LogicalClockBucket and the
///   next item in the stream as a count for that bucket.
///
/// * If the first bit is not set AND the second bit is set, this is
///   an event with metadata. Treat the next item in the stream as that
///   metadata.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct CompactLogItem(u32);

impl CompactLogItem {
    #[must_use]
    pub(crate) fn event(event_id: EventId) -> Self {
        // The construction checks for EventId should prevent the top bit from being set
        CompactLogItem(event_id.get_raw())
    }

    #[must_use]
    pub(crate) fn clock(clock: LogicalClock) -> (Self, Self) {
        // Set the top bit for id to indicate that it is not an event but a logical clock bucket,
        // and to treat the next item as the count. Don't separate these two!
        let id = clock.id | CLOCK_MASK;
        (CompactLogItem(id), CompactLogItem(clock.count))
    }

    #[must_use]
    pub(crate) fn event_with_metadata(event_id: EventId, meta: u32) -> (Self, Self) {
        (
            CompactLogItem(event_id.get_raw() | EVENT_WITH_META_MASK),
            CompactLogItem(meta),
        )
    }

    pub(crate) fn is_event_with_metadata(&self) -> bool {
        (self.0 & EVENT_WITH_META_MASK) == EVENT_WITH_META_MASK
    }

    pub(crate) fn is_clock(&self) -> bool {
        (self.0 & CLOCK_MASK) == CLOCK_MASK
    }

    pub(crate) fn raw(self) -> u32 {
        self.0
    }

    /// Unset that top bit to get the original tracer id back out
    pub(crate) fn interpret_as_logical_clock_tracer_id(self) -> u32 {
        self.0 & 0b0111_1111_1111_1111_1111_1111_1111_1111
    }
}
impl core::fmt::Debug for CompactLogItem {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!("CompactLogItem({})", self.0))
    }
}

pub(crate) fn split_next_segment(
    items: &'_ [CompactLogItem],
    local_tracer_id: TracerId,
) -> SplitSegment<'_> {
    // Split off the clock segments
    let mut num_clock_items = 0;
    for item in items.iter().step_by(2) {
        if item.is_clock() {
            if num_clock_items > 0 {
                // Use the local tracer id as a marker to identify when
                // there are two adjacent segments that have no intervening
                // events (i.e. the segments consist solely of clocks).
                if item.interpret_as_logical_clock_tracer_id() == local_tracer_id.get_raw() {
                    let (clock_region, rest) = items.split_at(num_clock_items);
                    return SplitSegment {
                        clock_region,
                        event_region: &[],
                        rest,
                    };
                } else {
                    num_clock_items += 2;
                }
            } else {
                num_clock_items += 2;
            }
        } else {
            break;
        }
    }
    let (clock_region, events_and_rest) = items.split_at(num_clock_items);

    // Find how many events there are before we either run out of items
    // or bump into another clock region
    let mut num_event_items = 0;
    for item in events_and_rest {
        if item.is_clock() {
            break;
        } else {
            num_event_items += 1;
        }
    }
    let (event_region, rest) = events_and_rest.split_at(num_event_items);
    SplitSegment {
        clock_region,
        event_region,
        rest,
    }
}

pub(crate) fn count_segments(items: &[CompactLogItem], local_tracer_id: TracerId) -> usize {
    let mut num_segments = 0;
    let mut segment = split_next_segment(items, local_tracer_id);
    while !segment.is_empty() {
        num_segments += 1;
        segment = split_next_segment(segment.rest, local_tracer_id);
    }
    num_segments
}

pub(crate) struct SplitSegment<'a> {
    pub(crate) clock_region: &'a [CompactLogItem],
    pub(crate) event_region: &'a [CompactLogItem],
    pub(crate) rest: &'a [CompactLogItem],
}

impl<'a> SplitSegment<'a> {
    fn is_empty(&self) -> bool {
        self.clock_region.is_empty() && self.event_region.is_empty() && self.rest.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compact event
    fn ce(e: u32) -> CompactLogItem {
        CompactLogItem::event(EventId::new(e).unwrap())
    }

    /// Compact logical clock bucket
    fn cb(id: u32, count: u32) -> (CompactLogItem, CompactLogItem) {
        CompactLogItem::clock(LogicalClock { id, count })
    }

    #[test]
    fn happy_path_segment_counting() {
        let tracer_id = TracerId::new(314).unwrap();
        assert_eq!(0, count_segments(&[], tracer_id));
        assert_eq!(1, count_segments(&[ce(1)], tracer_id));
        assert_eq!(1, count_segments(&[ce(1), ce(1)], tracer_id));
        assert_eq!(1, count_segments(&[ce(1), ce(2), ce(1)], tracer_id));

        let (a, b) = cb(1, 1);
        let (c, d) = cb(2, 1);
        assert_eq!(1, count_segments(&[a, b, ce(1)], tracer_id));
        assert_eq!(2, count_segments(&[ce(1), a, b], tracer_id));
        assert_eq!(2, count_segments(&[ce(1), a, b, ce(1)], tracer_id));
        assert_eq!(2, count_segments(&[a, b, ce(1), c, d], tracer_id));
        assert_eq!(
            2,
            count_segments(&[a, b, ce(1), c, d, ce(1), ce(2),], tracer_id)
        );
        let (e, f) = cb(3, 1);
        assert_eq!(
            2,
            count_segments(&[a, b, ce(1), c, d, e, f, ce(1), ce(2),], tracer_id)
        );
        assert_eq!(
            3,
            count_segments(&[a, b, ce(1), c, d, ce(1), ce(2), e, f,], tracer_id)
        );
    }

    #[test]
    fn segment_counting_distinguishes_adjacent_clock_segments_by_local_tracer_id() {
        let local_tracer_id = TracerId::new(314).unwrap();
        let (a, b) = cb(314, 1);
        assert_eq!(1, count_segments(&[a, b], local_tracer_id));
        let (c, d) = cb(314, 2);
        assert_eq!(2, count_segments(&[a, b, c, d], local_tracer_id));
        let (e, f) = cb(99, 2);
        assert_eq!(2, count_segments(&[a, b, c, d, e, f], local_tracer_id));
        assert_eq!(2, count_segments(&[a, b, e, f, c, d], local_tracer_id));
    }

    #[test]
    fn expected_representation() {
        let e = CompactLogItem::event(EventId::new(4).expect("Could not make EventId"));
        assert!(!e.is_clock());

        let (id, count) = CompactLogItem::clock(LogicalClock { id: 4, count: 5 });
        assert!(id.is_clock());
        assert!(!count.is_clock());
    }
}
