//! A compact in-memory format for representing a linear
//! history of logical clocks and events.
//!
//! This log is broken up into segments comprised
//! of 1 or more logical clocks followed by 0 or more
//! events. Events may or may not have associated payload
//! values.
//!
//! Contiguous logical clock segments are distinguished by
//! the use of a "local" id value that represents the id of
//! the location where the log was generated.
use super::{EventId, LogicalClock, TracerId};
use fixed_slice_vec::FixedSliceVec;

const CLOCK_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
const EVENT_WITH_PAYLOAD_MASK: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;

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
///   an event with payload. Treat the next item in the stream as that
///   payload.
#[derive(Clone, Copy, PartialEq)]
#[repr(transparent)]
pub struct CompactLogItem(u32);

impl CompactLogItem {
    /// Create a single event `CompactLogItem` with no payload
    #[must_use]
    #[inline]
    pub(crate) fn event(event_id: EventId) -> Self {
        // The construction checks for EventId should prevent the top bit from being set
        CompactLogItem(event_id.get_raw())
    }

    /// Create a logical-clock style pair of `CompactLogItem`s
    #[must_use]
    #[inline]
    pub fn clock(clock: LogicalClock) -> (Self, Self) {
        // Set the top bit for id to indicate that it is not an event but a logical clock bucket,
        // and to treat the next item as the count. Don't separate these two!
        let id = clock.id | CLOCK_MASK;
        (CompactLogItem(id), CompactLogItem(clock.count))
    }

    /// Create a pair of `CompactLogItem`s representing an event and associated payload.
    #[must_use]
    #[inline]
    pub(crate) fn event_with_payload(event_id: EventId, payload: u32) -> (Self, Self) {
        (
            CompactLogItem(event_id.get_raw() | EVENT_WITH_PAYLOAD_MASK),
            // We're just giving payload back out as is for now.
            CompactLogItem(payload),
        )
    }

    #[inline]
    pub(crate) fn has_clock_bit_set(self) -> bool {
        (self.0 & CLOCK_MASK) == CLOCK_MASK
    }

    #[inline]
    pub(crate) fn has_event_with_payload_bit_set(self) -> bool {
        (self.0 & EVENT_WITH_PAYLOAD_MASK) == EVENT_WITH_PAYLOAD_MASK
    }

    #[inline]
    pub(crate) fn raw(self) -> u32 {
        self.0
    }

    /// Rather tricky and dangerous to use, firmly recommend
    /// the more strongly typed constructors where possible.
    ///
    /// Pretty much should only see this in use when marshalling
    /// raw bytes around.
    #[inline]
    pub fn from_raw(value: u32) -> Self {
        CompactLogItem(value)
    }

    /// Unset that top bit to get the original tracer id back out
    #[inline]
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
        if item.has_clock_bit_set() {
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
    let mut expecting_payload = false;
    for item in events_and_rest {
        if expecting_payload {
            // Don't inspect the payload content
            expecting_payload = false;
            num_event_items += 1;
        } else if item.has_clock_bit_set() {
            // Reached a clock region, this segment is over
            break;
        } else {
            num_event_items += 1;
            if item.has_event_with_payload_bit_set() {
                expecting_payload = true;
            }
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
    LogSegmentIterator::new(local_tracer_id, items).count()
}

#[derive(Debug)]
pub(crate) struct SplitSegment<'a> {
    pub(crate) clock_region: &'a [CompactLogItem],
    pub(crate) event_region: &'a [CompactLogItem],
    pub(crate) rest: &'a [CompactLogItem],
}

/// Iterator over log segments
pub struct LogSegmentIterator<'a> {
    /// The tracer/location id used to distinguish between
    /// contiguous segments blocks of logical clocks
    local_tracer_id: TracerId,
    rest: &'a [CompactLogItem],
}

impl<'a> LogSegmentIterator<'a> {
    /// Create a per-segment iterator over a compact log slice.
    /// `source_tracer_id` should be the TracerId of the location where this log was generated
    pub fn new(source_tracer_id: TracerId, log: &'a [CompactLogItem]) -> LogSegmentIterator<'a> {
        LogSegmentIterator {
            local_tracer_id: source_tracer_id,
            rest: log,
        }
    }
}

impl<'a> Iterator for LogSegmentIterator<'a> {
    type Item = LogSegment<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rest.is_empty() {
            return None;
        }
        let split_segment = split_next_segment(self.rest, self.local_tracer_id);
        self.rest = split_segment.rest;
        if split_segment.clock_region.is_empty() && split_segment.event_region.is_empty() {
            return None;
        }
        Some(LogSegment {
            clock_region: split_segment.clock_region,
            event_region: split_segment.event_region,
        })
    }
}

/// A segment in the log, comprised of 1 or more LogicalClocks
/// followed by 0 or more events.
pub struct LogSegment<'a> {
    clock_region: &'a [CompactLogItem],
    event_region: &'a [CompactLogItem],
}

impl<'a> LogSegment<'a> {
    /// Iterate through the logical clocks in this segment
    pub fn iter_clocks(&self) -> LogSegmentLogicalClockIterator<'a> {
        LogSegmentLogicalClockIterator {
            remaining_clock_region: self.clock_region,
        }
    }
    /// Iterate through the logical events in this segment
    pub fn iter_events(&self) -> LogSegmentEventIterator<'a> {
        LogSegmentEventIterator {
            remaining_event_region: self.event_region,
        }
    }
}

/// Iterator for iterating through the logical clocks in a given compact log segment
pub struct LogSegmentLogicalClockIterator<'a> {
    remaining_clock_region: &'a [CompactLogItem],
}

impl<'a> Iterator for LogSegmentLogicalClockIterator<'a> {
    type Item = LogicalClock;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_clock_region.len() < 2 {
            return None;
        }
        let (curr, remainder) = self.remaining_clock_region.split_at(2);
        self.remaining_clock_region = remainder;
        Some(LogicalClock {
            // TODO - switch LogicalClock to use TracerId for id, since it should be repr(transparent),
            // which repr(C) should be able to handle just fine
            id: curr[0].interpret_as_logical_clock_tracer_id(),
            count: curr[1].raw(),
        })
    }
}

/// Iterator for iterating through the events in a given compact log segment
pub struct LogSegmentEventIterator<'a> {
    remaining_event_region: &'a [CompactLogItem],
}

/// The sanity checks that might fail when interpreting the compact log format
/// into a concrete stream of events.
#[derive(Debug)]
pub enum LogEventInterpretationError {
    /// The event id was not in the allowed ekotrace::EventId ranges
    InvalidEventId(u32),
    /// An event with the "has a payload" flag was found, but the payload-bearing
    /// log item expected next was not present. This may happen when iterating
    /// over an incomplete or incorrectly segmented slice of compact log items.
    EventMissingPayload(EventId),
}

impl<'a> Iterator for LogSegmentEventIterator<'a> {
    type Item = Result<LogEvent, LogEventInterpretationError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((first, remaining)) = self.remaining_event_region.split_first() {
            self.remaining_event_region = remaining;
            let raw_ev = first.raw();
            if first.has_event_with_payload_bit_set() {
                let event_expecting_payload = raw_ev & !EVENT_WITH_PAYLOAD_MASK;
                let event_expecting_payload = EventId::new(event_expecting_payload)
                    .or_else(|| EventId::new_internal(event_expecting_payload))
                    .ok_or_else(|| {
                        LogEventInterpretationError::InvalidEventId(event_expecting_payload)
                    });
                if let Some((second, remaining)) = self.remaining_event_region.split_first() {
                    self.remaining_event_region = remaining;
                    Some(
                        event_expecting_payload
                            .map(|event_id| LogEvent::EventWithPayload(event_id, second.raw())),
                    )
                } else {
                    Some(match event_expecting_payload {
                        Ok(event_id) => {
                            Err(LogEventInterpretationError::EventMissingPayload(event_id))
                        }
                        Err(e) => Err(e),
                    })
                }
            } else {
                Some(
                    EventId::new(raw_ev)
                        .or_else(|| EventId::new_internal(raw_ev))
                        .ok_or_else(|| LogEventInterpretationError::InvalidEventId(raw_ev))
                        .map(LogEvent::Event),
                )
            }
        } else {
            None
        }
    }
}

/// An event in the log
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LogEvent {
    /// An event consisting only of an id
    Event(EventId),
    /// An event id paired with a data payload
    EventWithPayload(EventId, u32),
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
        assert!(!e.has_clock_bit_set());

        let (id, count) = CompactLogItem::clock(LogicalClock { id: 4, count: 5 });
        assert!(id.has_clock_bit_set());
        assert!(!count.has_clock_bit_set());
    }

    #[test]
    fn payload_events_are_well_represented() {
        let (ev, payload) = CompactLogItem::event_with_payload(EventId::new(4).unwrap(), 777);
        assert_eq!(ev.0 & EVENT_WITH_PAYLOAD_MASK, EVENT_WITH_PAYLOAD_MASK);
        assert_eq!(payload.0, 777);
    }
}
