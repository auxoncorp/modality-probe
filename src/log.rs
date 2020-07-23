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

    /// Unset that top bit to get the original probe id back out
    #[inline]
    pub(crate) fn interpret_as_logical_clock_probe_id(self) -> u32 {
        self.0 & !CLOCK_MASK
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
