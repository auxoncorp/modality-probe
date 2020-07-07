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
//! the probe where the log was generated.

use super::{EventId, LogicalClock, ProbeId};
use core::convert::TryInto;
use fixed_slice_vec::FixedSliceVec;

const CLOCK_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
const EVENT_WITH_PAYLOAD_MASK: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;

pub(crate) type CompactLogVec<'a> = FixedSliceVec<'a, CompactLogItem>;

/// In a stream of these:
/// * If first bit is not set AND the second bit is not set, this is a
///   plain event id.
///
/// * If the first bit is set AND the second bit is not set, treat the
///   rest of the value as a ProbeId for a LogicalClockBucket and the
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
    pub const fn event(event_id: EventId) -> Self {
        // The construction checks for EventId should prevent the top bit from being set
        CompactLogItem(event_id.get_raw())
    }

    /// Create a logical-clock style pair of `CompactLogItem`s
    #[must_use]
    #[inline]
    pub fn clock(clock: LogicalClock) -> (Self, Self) {
        // Set the top bit for id to indicate that it is not an event but a logical clock bucket,
        // and to treat the next item as the count. Don't separate these two!
        let id = clock.id.get_raw() | CLOCK_MASK;
        (CompactLogItem(id), CompactLogItem(clock.count))
    }

    /// Create a pair of `CompactLogItem`s representing an event and associated payload.
    #[must_use]
    #[inline]
    pub fn event_with_payload(event_id: EventId, payload: u32) -> (Self, Self) {
        (
            CompactLogItem(event_id.get_raw() | EVENT_WITH_PAYLOAD_MASK),
            // We're just giving payload back out as is for now.
            CompactLogItem(payload),
        )
    }

    /// Return true if the log item has its clock bit set
    #[inline]
    pub fn has_clock_bit_set(self) -> bool {
        (self.0 & CLOCK_MASK) == CLOCK_MASK
    }

    /// Return true if the log item has its 'event with payload' bit set
    #[inline]
    pub fn has_event_with_payload_bit_set(self) -> bool {
        (self.0 & EVENT_WITH_PAYLOAD_MASK) == EVENT_WITH_PAYLOAD_MASK
    }

    /// Get the u32 representation of the log item
    #[inline]
    pub fn raw(self) -> u32 {
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

    /// Unset that top bit to get the original probe id back out
    #[inline]
    pub fn interpret_as_logical_clock_probe_id(self) -> u32 {
        self.0 & !CLOCK_MASK
    }
}
impl core::fmt::Debug for CompactLogItem {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!("CompactLogItem({})", self.0))
    }
}

impl race_buffer::Entry for CompactLogItem {
    fn is_prefix(&self) -> bool {
        self.has_clock_bit_set() || self.has_event_with_payload_bit_set()
    }
}

pub(crate) fn split_next_segment(
    items: &'_ [CompactLogItem],
    local_probe_id: ProbeId,
) -> SplitSegment<'_> {
    // Split off the clock segments
    let mut num_clock_items = 0;
    for item in items.iter().step_by(2) {
        if item.has_clock_bit_set() {
            if num_clock_items > 0 {
                // Use the local probe id as a marker to identify when
                // there are two adjacent segments that have no intervening
                // events (i.e. the segments consist solely of clocks).
                if item.interpret_as_logical_clock_probe_id() == local_probe_id.get_raw() {
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

#[derive(Debug)]
pub(crate) struct SplitSegment<'a> {
    pub(crate) clock_region: &'a [CompactLogItem],
    pub(crate) event_region: &'a [CompactLogItem],
    pub(crate) rest: &'a [CompactLogItem],
}

/// Iterator over log segments
pub struct LogSegmentIterator<'a> {
    /// The probe id used to distinguish between
    /// contiguous segments blocks of logical clocks
    local_probe_id: ProbeId,
    rest: &'a [CompactLogItem],
}

impl<'a> LogSegmentIterator<'a> {
    /// Create a per-segment iterator over a compact log slice.
    /// `source_probe_id` should be the ProbeId of the probe where this log was generated
    pub fn new(source_probe_id: ProbeId, log: &'a [CompactLogItem]) -> LogSegmentIterator<'a> {
        LogSegmentIterator {
            local_probe_id: source_probe_id,
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
        let split_segment = split_next_segment(self.rest, self.local_probe_id);
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
    type Item = Result<LogicalClock, LogicalClockInterpretationError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_clock_region.is_empty() {
            return None;
        }
        if self.remaining_clock_region.len() == 1 {
            let raw_id = self.remaining_clock_region[0].interpret_as_logical_clock_probe_id();
            return match ProbeId::new(raw_id) {
                Some(id) => Some(Err(LogicalClockInterpretationError::ClockMissingCount(id))),
                None => Some(Err(LogicalClockInterpretationError::InvalidProbeId(raw_id))),
            };
        }

        let (curr, remainder) = self.remaining_clock_region.split_at(2);
        self.remaining_clock_region = remainder;
        let raw_id = curr[0].interpret_as_logical_clock_probe_id();
        let id = match ProbeId::new(raw_id) {
            Some(id) => id,
            None => return Some(Err(LogicalClockInterpretationError::InvalidProbeId(raw_id))),
        };

        Some(Ok(LogicalClock {
            id,
            count: curr[1].raw(),
        }))
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
    /// The event id was not in the allowed modality_probe::EventId ranges
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
                let event_expecting_payload = event_expecting_payload.try_into().map_err(|_e| {
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
                    raw_ev
                        .try_into()
                        .map_err(|_e| LogEventInterpretationError::InvalidEventId(raw_ev))
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

/// An item in the log, fully materialized
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum LogItem {
    /// A logical clock
    Clock(LogicalClock),
    /// An event, with or without a payload
    LogEvent(LogEvent),
}

/// An iterator adapter that produces fully expanded `LogItem`s by interpreting an iterator over
/// `CompactLogItem`s
pub struct LogItemIterator<I> {
    inner: I,
    is_done: bool,
}

impl<I> LogItemIterator<I>
where
    I: Iterator<Item = CompactLogItem>,
{
    /// Create an iterator adapter that produces fully expanded `LogItem`s by interpreting an iterator over
    /// `CompactLogItem`s
    pub fn new(compact_log_item_iterator: I) -> Self {
        LogItemIterator {
            inner: compact_log_item_iterator,
            is_done: false,
        }
    }
}
/// Converting from compact log to logical clocks can fail if
/// the compact log was created wrong. Here's how.
#[derive(Debug, PartialEq, Eq)]
pub enum LogicalClockInterpretationError {
    /// The id was not in the allowed modality_probe::ProbeId range
    InvalidProbeId(u32),
    /// A logical clock id was found, but the count-bearing
    /// log item expected next was not present. This may happen when iterating
    /// over an incomplete or incorrectly segmented slice of compact log items.
    ClockMissingCount(ProbeId),
}

/// The sanity checks that might fail when interpreting the compact log format
/// into a concrete stream of items (clocks and events).
#[derive(Debug)]
pub enum LogItemInterpretationError {
    /// What might fail when interpreting the compact log format
    /// into events.
    LogEventInterpretationError(LogEventInterpretationError),
    /// What might fail when interpreting the compact log format
    /// into clocks.
    LogicalClockInterpretationError(LogicalClockInterpretationError),
}

impl From<LogEventInterpretationError> for LogItemInterpretationError {
    fn from(e: LogEventInterpretationError) -> Self {
        LogItemInterpretationError::LogEventInterpretationError(e)
    }
}

impl From<LogicalClockInterpretationError> for LogItemInterpretationError {
    fn from(e: LogicalClockInterpretationError) -> Self {
        LogItemInterpretationError::LogicalClockInterpretationError(e)
    }
}

impl<I> Iterator for LogItemIterator<I>
where
    I: Iterator<Item = CompactLogItem>,
{
    type Item = Result<LogItem, LogItemInterpretationError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_done {
            return None;
        }
        let compact = match self.inner.next() {
            Some(compact) => compact,
            None => {
                self.is_done = true;
                return None;
            }
        };

        if compact.has_clock_bit_set() {
            let raw_id = compact.interpret_as_logical_clock_probe_id();
            let id = match ProbeId::new(raw_id) {
                Some(id) => id,
                None => {
                    self.is_done = true;
                    return Some(Err(
                        LogItemInterpretationError::LogicalClockInterpretationError(
                            LogicalClockInterpretationError::InvalidProbeId(raw_id),
                        ),
                    ));
                }
            };
            match self.inner.next() {
                Some(count) => Some(Ok(LogItem::Clock(LogicalClock {
                    id,
                    count: count.raw(),
                }))),
                None => {
                    self.is_done = true;
                    Some(Err(
                        LogItemInterpretationError::LogicalClockInterpretationError(
                            LogicalClockInterpretationError::ClockMissingCount(id),
                        ),
                    ))
                }
            }
        } else if compact.has_event_with_payload_bit_set() {
            let event_id = compact.raw() & !EVENT_WITH_PAYLOAD_MASK;
            let event_id: EventId = match event_id.try_into() {
                Ok(id) => id,
                Err(_) => {
                    self.is_done = true;
                    return Some(Err(
                        LogItemInterpretationError::LogEventInterpretationError(
                            LogEventInterpretationError::InvalidEventId(event_id),
                        ),
                    ));
                }
            };
            match self.inner.next() {
                Some(payload) => Some(Ok(LogItem::LogEvent(LogEvent::EventWithPayload(
                    event_id,
                    payload.raw(),
                )))),
                None => {
                    self.is_done = true;
                    Some(Err(
                        LogItemInterpretationError::LogEventInterpretationError(
                            LogEventInterpretationError::EventMissingPayload(event_id),
                        ),
                    ))
                }
            }
        } else {
            let event_id = compact.raw();
            match event_id.try_into() {
                Ok(event_id) => Some(Ok(LogItem::LogEvent(LogEvent::Event(event_id)))),
                Err(_) => {
                    self.is_done = true;
                    Some(Err(
                        LogItemInterpretationError::LogEventInterpretationError(
                            LogEventInterpretationError::InvalidEventId(event_id),
                        ),
                    ))
                }
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod log_tests {
    use super::*;
    use crate::id::id_tests::*;
    use proptest::prelude::*;
    use proptest::std_facade::*;

    /// Compact event
    fn ce(e: u32) -> CompactLogItem {
        CompactLogItem::event(e.try_into().unwrap())
    }

    /// Compact event with payload
    fn cep(e: u32, v: u32) -> (CompactLogItem, CompactLogItem) {
        CompactLogItem::event_with_payload(e.try_into().unwrap(), v)
    }

    /// Compact logical clock bucket
    fn cb(id: u32, count: u32) -> (CompactLogItem, CompactLogItem) {
        CompactLogItem::clock(LogicalClock {
            id: id.try_into().unwrap(),
            count,
        })
    }

    fn count_segments(log_items: &[CompactLogItem], probe_id: ProbeId) -> usize {
        LogSegmentIterator::new(probe_id, log_items).count()
    }

    #[test]
    fn happy_path_segment_counting() {
        let probe_id = ProbeId::new(314).unwrap();
        assert_eq!(0, count_segments(&[], probe_id));
        assert_eq!(1, count_segments(&[ce(1)], probe_id));
        assert_eq!(1, count_segments(&[ce(1), ce(1)], probe_id));
        assert_eq!(1, count_segments(&[ce(1), ce(2), ce(1)], probe_id));

        let (a, b) = cb(1, 1);
        let (c, d) = cb(2, 1);
        assert_eq!(1, count_segments(&[a, b, ce(1)], probe_id));
        assert_eq!(2, count_segments(&[ce(1), a, b], probe_id));
        assert_eq!(2, count_segments(&[ce(1), a, b, ce(1)], probe_id));
        assert_eq!(2, count_segments(&[a, b, ce(1), c, d], probe_id));
        assert_eq!(
            2,
            count_segments(&[a, b, ce(1), c, d, ce(1), ce(2),], probe_id)
        );
        let (e, f) = cb(3, 1);
        assert_eq!(
            2,
            count_segments(&[a, b, ce(1), c, d, e, f, ce(1), ce(2),], probe_id)
        );
        assert_eq!(
            3,
            count_segments(&[a, b, ce(1), c, d, ce(1), ce(2), e, f,], probe_id)
        );
    }

    #[test]
    fn segment_counting_distinguishes_adjacent_clock_segments_by_local_probe_id() {
        let local_probe_id = ProbeId::new(314).unwrap();
        let (a, b) = cb(314, 1);
        assert_eq!(1, count_segments(&[a, b], local_probe_id));
        let (c, d) = cb(314, 2);
        assert_eq!(2, count_segments(&[a, b, c, d], local_probe_id));
        let (e, f) = cb(99, 2);
        assert_eq!(2, count_segments(&[a, b, c, d, e, f], local_probe_id));
        assert_eq!(2, count_segments(&[a, b, e, f, c, d], local_probe_id));
    }

    #[test]
    fn segmentation_distinguishes_events_with_payloads_from_clocks() {
        let local_probe_id = ProbeId::new(314).unwrap();
        let (a, b) = cb(314, 1);
        let (c, d) = cep(99, core::u32::MAX);
        assert_eq!(1, count_segments(&[a, b, c, d], local_probe_id));
    }

    #[test]
    fn expected_representation() {
        let e = CompactLogItem::event(EventId::new(4).expect("Could not make EventId"));
        assert!(!e.has_clock_bit_set());

        let (id, count) = CompactLogItem::clock(LogicalClock {
            id: 4.try_into().unwrap(),
            count: 5,
        });
        assert!(id.has_clock_bit_set());
        assert!(!count.has_clock_bit_set());
    }

    #[test]
    fn payload_events_are_well_represented() {
        let (ev, payload) = CompactLogItem::event_with_payload(EventId::new(4).unwrap(), 777);
        assert_eq!(ev.0 & EVENT_WITH_PAYLOAD_MASK, EVENT_WITH_PAYLOAD_MASK);
        assert_eq!(payload.0, 777);
    }

    #[test]
    fn can_iterate_through_internal_events() {
        let raw_event = EventId::MAX_INTERNAL_ID;
        let segment = LogSegment {
            clock_region: &[],
            event_region: &[ce(raw_event)],
        };
        let mut iter = segment.iter_events();
        assert_eq!(
            LogEvent::Event(EventId::new_internal(raw_event).unwrap()),
            iter.next().unwrap().unwrap()
        );
        assert!(iter.next().is_none());
    }

    prop_compose! {
        pub(crate) fn gen_events(max_events: usize)(vec in proptest::collection::vec(gen_log_event(), 0..max_events)) -> Vec<LogEvent> {
            vec
        }
    }

    pub(crate) fn gen_log_event() -> impl Strategy<Value = LogEvent> {
        prop_oneof![
            gen_raw_internal_event_id()
                .prop_map(|id| LogEvent::Event(EventId::new_internal(id).unwrap())),
            (gen_raw_internal_event_id(), any::<u32>()).prop_map(|(id, payload)| {
                LogEvent::EventWithPayload(EventId::new_internal(id).unwrap(), payload)
            }),
            gen_raw_user_event_id().prop_map(|id| LogEvent::Event(EventId::new(id).unwrap())),
            (gen_raw_user_event_id(), any::<u32>()).prop_map(|(id, payload)| {
                LogEvent::EventWithPayload(EventId::new(id).unwrap(), payload)
            }),
        ]
    }

    prop_compose! {
        pub(crate) fn gen_clock()(id in gen_probe_id(), count in proptest::num::u32::ANY) -> LogicalClock {
            LogicalClock { id, count }
        }
    }

    pub(crate) fn events_to_log(events: Vec<LogEvent>) -> Vec<CompactLogItem> {
        let mut log = Vec::with_capacity(events.len() * 2);
        for event in events {
            match event {
                LogEvent::Event(e) => {
                    log.push(CompactLogItem::event(e));
                }
                LogEvent::EventWithPayload(e, p) => {
                    let (e, p) = CompactLogItem::event_with_payload(e, p);
                    log.push(e);
                    log.push(p);
                }
            }
        }
        log
    }

    pub(crate) fn clocks_to_log(clocks: Vec<LogicalClock>) -> Vec<CompactLogItem> {
        let mut log = Vec::with_capacity(clocks.len() * 2);
        for clock in clocks {
            let (id, count) = CompactLogItem::clock(clock);
            log.push(id);
            log.push(count);
        }
        log
    }

    #[derive(Clone, Debug, PartialEq)]
    pub(crate) struct OwnedLogSegment {
        pub clocks: Vec<LogicalClock>,
        pub events: Vec<LogEvent>,
    }

    prop_compose! {
        fn gen_segment(max_clocks: usize, max_events: usize)
            (clocks in prop::collection::vec(gen_clock(), 1..max_clocks),
                events in prop::collection::vec(gen_log_event(), 0..max_events)) -> OwnedLogSegment {
            OwnedLogSegment {
                clocks,
                events,
            }
        }
    }

    prop_compose! {
        fn gen_segments(
            max_length: usize,
            max_clocks_per_segment: usize,
            max_events_per_segment: usize)
            (vec in prop::collection::vec(gen_segment(max_clocks_per_segment, max_events_per_segment), 0..max_length))
                -> Vec<OwnedLogSegment> {
            vec
        }
    }

    prop_compose! {
        pub(crate) fn gen_compact_log(
            max_segments: usize,
            max_clocks_per_segment: usize,
            max_events_per_segment: usize)
            (segments in gen_segments(max_segments, max_clocks_per_segment, max_events_per_segment)) -> Vec<CompactLogItem> {
                let mut log = Vec::with_capacity(max_segments * (max_clocks_per_segment + max_events_per_segment));
                for segment in segments {
                    log.extend(clocks_to_log(segment.clocks));
                    log.extend(events_to_log(segment.events));
                }
                log
            }
    }

    proptest! {
        #[test]
        fn arbitrary_log_segment_iterable(probe_id in gen_probe_id(), log in gen_compact_log(25, 257, 514)) {
            // Note the max segments, max clocks-per-segment and max events-per-segment values
            // above are pulled completely from a hat
            let seg_iter = LogSegmentIterator::new(probe_id, &log);
            let mut n: usize = 0;
            for seg in seg_iter {
                for c in seg.iter_clocks() {
                    let _clock = c.expect("Should be able to interpret all the clocks");
                    n = n.saturating_add(2);
                }
                for e in seg.iter_events() {
                    let log_event = e.expect("Should be able to interpret all the events");
                    n = n.saturating_add(match log_event {
                        LogEvent::Event(_) => 1,
                        LogEvent::EventWithPayload(_, _) => 2,
                    });
                }
            }
            assert_eq!(n, log.len());
        }
    }

    proptest! {
        #[test]
        fn arbitrary_log_item_iterable(log in gen_compact_log(25, 257, 514)) {
            // Note the max segments, max clocks-per-segment and max events-per-segment values
            // above are pulled completely from a hat
            let log_len = log.len();
            let iter = LogItemIterator::new(log.into_iter());
            let mut n: usize = 0;
            for item_result in iter {
                let item = item_result.expect("Should be able to interpret all the items");
                n = n.saturating_add(match item {
                    LogItem::Clock(_) => 2,
                    LogItem::LogEvent(e) => match e {
                        LogEvent::Event(_) => 1,
                        LogEvent::EventWithPayload(_, _) => 2,
                    },
                });
            }
            assert_eq!(n, log_len);
        }
    }

    proptest! {
        #[test]
        fn arbitrary_events_in_log_round_trippable(probe_id in gen_probe_id(), events in gen_events(514)) {
            let log = events_to_log(events.clone());
            let mut seg_iter = LogSegmentIterator::new(probe_id, &log);
            if events.is_empty() {
                assert!(seg_iter.next().is_none());
            } else {
                let seg = seg_iter.next().unwrap();
                let found_events:Vec<LogEvent> = seg.iter_events().map(|event_result| event_result.expect("Could not iterate through events correctly")).collect();
                assert_eq!(events, found_events);
                assert!(seg_iter.next().is_none());
            }
        }
    }
}
