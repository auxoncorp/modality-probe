//! Types and functionality used for the probe's event storage.

use race_buffer::{writer::RaceBuffer, Entry};

use crate::{pack_clock_word, EventId, LogicalClock};

const CLOCK_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
const EVENT_WITH_PAYLOAD_MASK: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;

pub(crate) type RaceLog<'a> = RaceBuffer<'a, LogEntry>;

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
pub struct LogEntry(u32);

impl LogEntry {
    /// Construct an entry without knowing what kind it is.
    ///
    /// # Safety
    ///
    /// This should be used with caution, for cases where you
    /// want to use `LogEntry` to determine the "type" of the raw
    /// value.
    pub unsafe fn new_unchecked(val: u32) -> Self {
        LogEntry(val)
    }

    /// Create a single event `LogEntry` with no payload.
    #[must_use]
    #[inline]
    pub fn event(event_id: EventId) -> Self {
        // The construction checks for EventId should prevent the top bit from being set
        LogEntry(event_id.get_raw())
    }

    /// Create a logical-clock style pair of `LogEntry`s
    #[must_use]
    #[inline]
    pub fn clock(clock: LogicalClock) -> (Self, Self) {
        // Set the top bit for id to indicate that it is not an event but a logical clock bucket,
        // and to treat the next item as the count. Don't separate these two!
        let id = clock.id.get_raw() | CLOCK_MASK;
        (
            LogEntry(id),
            LogEntry(pack_clock_word(clock.epoch, clock.ticks)),
        )
    }

    /// Create a pair of `LogEntry`s representing an event and
    /// associated payload.
    #[must_use]
    #[inline]
    pub fn event_with_payload(event_id: EventId, payload: u32) -> (Self, Self) {
        (
            LogEntry(event_id.get_raw() | EVENT_WITH_PAYLOAD_MASK),
            // We're just giving payload back out as is for now.
            LogEntry(payload),
        )
    }

    /// Determine if the clock bit is set on this entry.
    #[inline]
    pub fn has_clock_bit_set(self) -> bool {
        (self.0 & CLOCK_MASK) == CLOCK_MASK
    }

    /// Determine if the event with payload bit is set on this entry.
    #[inline]
    pub fn has_event_with_payload_bit_set(self) -> bool {
        (self.0 & EVENT_WITH_PAYLOAD_MASK) == EVENT_WITH_PAYLOAD_MASK
    }

    #[inline]
    pub(crate) fn raw(self) -> u32 {
        self.0
    }

    /// Unset that top bit to get the original probe id back out
    #[inline]
    pub fn interpret_as_logical_clock_probe_id(self) -> u32 {
        self.0 & !CLOCK_MASK
    }

    /// Convert to an event id.
    pub fn interpret_as_event_id(&self) -> Option<EventId> {
        EventId::new(self.0)
    }
}

impl core::fmt::Debug for LogEntry {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!("LogEntry({})", self.0))
    }
}

impl Entry for LogEntry {
    fn is_prefix(&self) -> bool {
        self.has_clock_bit_set() || self.has_event_with_payload_bit_set()
    }
}

#[cfg(test)]
pub(crate) mod log_tests {
    use super::*;
    use crate::id::id_tests::*;
    use crate::{ProbeEpoch, ProbeId, ProbeTicks};
    use proptest::prelude::*;

    prop_compose! {
        pub(crate) fn gen_clock()(
            id in gen_probe_id(),
            epoch in gen_probe_epoch(),
            ticks in gen_probe_ticks()
        ) -> LogicalClock {
            LogicalClock { id, epoch, ticks }
        }
    }

    #[test]
    fn expected_representation() {
        let e = LogEntry::event(EventId::new(4).expect("Could not make EventId"));
        assert!(!e.has_clock_bit_set());

        let (id, count) = LogEntry::clock(LogicalClock {
            id: ProbeId::new(4).unwrap(),
            epoch: ProbeEpoch(0),
            ticks: ProbeTicks(5),
        });
        assert!(id.has_clock_bit_set());
        assert!(!count.has_clock_bit_set());
    }

    #[test]
    fn payload_events_are_well_represented() {
        let (ev, payload) = LogEntry::event_with_payload(EventId::new(4).unwrap(), 777);
        assert_eq!(ev.0 & EVENT_WITH_PAYLOAD_MASK, EVENT_WITH_PAYLOAD_MASK);
        assert_eq!(payload.0, 777);
    }
}
