//! Types and functionality used for the probe's event storage.

use crate::{pack_clock_word, time::Nanoseconds, EventId, LogicalClock};
use fenced_ring_buffer::FencedRingBuffer;

pub(crate) const CLOCK_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;
pub(crate) const EVENT_WITH_PAYLOAD_MASK: u32 = 0b0100_0000_0000_0000_0000_0000_0000_0000;
pub(crate) const WALL_CLOCK_TIME_MASK: u32 = 0b1100_0000_0000_0000_0000_0000_0000_0000;
pub(crate) const PAIRED_WALL_CLOCK_TIME_MASK: u32 = 0b0010_0000_0000_0000_0000_0000_0000_0000;
pub(crate) const RESERVED_BITS_MASK: u32 = 0b1100_0000_0000_0000_0000_0000_0000_0000;

/// FencedRingBuffer used to store log entries at each probe
pub type LogBuffer<'a> = FencedRingBuffer<'a, LogEntry>;

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

    /// Create a pair of `LogEntry`s representing paired wall clock time.
    ///
    /// The first entry contains the `NanosecondsHighBits` of the
    /// time along with the upper mask bits and paired flag bit `0b111`.
    /// The second entry contains the `NanosecondsLowBits` of the time.
    ///
    /// NOTE: paired wall clock time entries should *always* precede the
    /// other entry it's associated with (event, event-with-payload, trace-clock, etc).
    #[must_use]
    #[inline]
    pub fn paired_wall_clock_time(time: Nanoseconds) -> (Self, Self) {
        let (low_bits, high_bits) = time.split();
        (
            LogEntry(
                u32::from_le_bytes(high_bits.0)
                    | WALL_CLOCK_TIME_MASK
                    | PAIRED_WALL_CLOCK_TIME_MASK,
            ),
            LogEntry(u32::from_le_bytes(low_bits.0)),
        )
    }

    /// Create a pair of `LogEntry`s representing unpaired wall clock time.
    ///
    /// The first entry contains the `NanosecondsHighBits` of the
    /// time along with the upper mask bits and unpaired flag bit `0b110`.
    /// The second entry contains the `NanosecondsLowBits` of the time.
    /// Create a pair of `LogEntry`s representing wall clock time.
    #[must_use]
    #[inline]
    pub fn unpaired_wall_clock_time(time: Nanoseconds) -> (Self, Self) {
        let (low_bits, high_bits) = time.split();
        (
            LogEntry(
                (u32::from_le_bytes(high_bits.0) | WALL_CLOCK_TIME_MASK)
                    & !PAIRED_WALL_CLOCK_TIME_MASK,
            ),
            LogEntry(u32::from_le_bytes(low_bits.0)),
        )
    }

    /// Determine if the clock bit is set on this entry.
    #[inline]
    pub fn has_clock_bit_set(self) -> bool {
        (self.0 & RESERVED_BITS_MASK) == CLOCK_MASK
    }

    /// Determine if the event with payload bit is set on this entry.
    #[inline]
    pub fn has_event_with_payload_bit_set(self) -> bool {
        (self.0 & RESERVED_BITS_MASK) == EVENT_WITH_PAYLOAD_MASK
    }

    /// Determine if the wall clock time bits (paired or unpaired) are set on this entry.
    #[inline]
    pub fn has_wall_clock_time_bits_set(self) -> bool {
        (self.0 & RESERVED_BITS_MASK) == WALL_CLOCK_TIME_MASK
    }

    /// Determine if the wall clock time paired bit is set on this entry.
    #[inline]
    pub fn has_wall_clock_time_paired_bit_set(self) -> bool {
        let mask = WALL_CLOCK_TIME_MASK | PAIRED_WALL_CLOCK_TIME_MASK;
        (self.0 & mask) == mask
    }

    /// Get the underlying value as a convenient primitive.
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Unset the top reserved bits to get the original probe id back out.
    #[inline]
    pub fn interpret_as_logical_clock_probe_id(self) -> u32 {
        self.0 & !CLOCK_MASK
    }

    /// Convert to an event id.
    #[inline]
    pub fn interpret_as_event_id(&self) -> Option<EventId> {
        let id = self.0 & !EVENT_WITH_PAYLOAD_MASK;
        EventId::new(id).or_else(|| EventId::new_internal(id))
    }

    /// Unset the top mask bits to get the original time high bits back out.
    #[inline]
    pub fn interpret_as_wall_clock_time_high_bits(self) -> u32 {
        let mask = WALL_CLOCK_TIME_MASK | PAIRED_WALL_CLOCK_TIME_MASK;
        self.0 & !mask
    }
}

impl core::fmt::Debug for LogEntry {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!("LogEntry({})", self.0))
    }
}

impl fenced_ring_buffer::Entry for LogEntry {
    // Payloads or clocks count entries could be interpreted as a prefix, but the FencedRingBuffer
    // will never call is_prefix on the entry after a prefix
    fn is_prefix(&self) -> bool {
        self.0 & RESERVED_BITS_MASK != 0
    }
}

#[cfg(test)]
pub(crate) mod log_tests {
    use super::*;
    use crate::{ProbeEpoch, ProbeId, ProbeTicks};

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

    #[test]
    fn wall_clock_time_are_well_represented() {
        let (high, low) = LogEntry::paired_wall_clock_time(Nanoseconds::new(1).unwrap());
        assert_eq!(high.0 & WALL_CLOCK_TIME_MASK, WALL_CLOCK_TIME_MASK);
        assert_eq!(
            high.0 & PAIRED_WALL_CLOCK_TIME_MASK,
            PAIRED_WALL_CLOCK_TIME_MASK
        );
        assert_eq!(low.0, 1);

        assert_eq!(
            LogEntry(PAIRED_WALL_CLOCK_TIME_MASK).has_wall_clock_time_paired_bit_set(),
            false
        );
        assert_eq!(
            LogEntry(PAIRED_WALL_CLOCK_TIME_MASK).has_wall_clock_time_bits_set(),
            false
        );
        assert_eq!(
            LogEntry(WALL_CLOCK_TIME_MASK | PAIRED_WALL_CLOCK_TIME_MASK)
                .has_wall_clock_time_paired_bit_set(),
            true
        );
        assert_eq!(
            LogEntry(WALL_CLOCK_TIME_MASK).has_wall_clock_time_bits_set(),
            true
        );
    }

    #[test]
    fn prefixes() {
        use fenced_ring_buffer::Entry;
        assert!(LogEntry::clock(LogicalClock {
            id: ProbeId::new(4).unwrap(),
            epoch: ProbeEpoch(0),
            ticks: ProbeTicks(5),
        })
        .0
        .is_prefix());
        assert!(LogEntry::event_with_payload(EventId::new(4).unwrap(), 777)
            .0
            .is_prefix());
        assert!(
            LogEntry::paired_wall_clock_time(Nanoseconds::new(0).unwrap())
                .0
                .is_prefix()
        );
    }
}
