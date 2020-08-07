use crate::{log::LogEntry, EventId, LogicalClock};
use core::convert::From;
use core::mem::MaybeUninit;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum OverwrittenEntry {
    /// No entry was overwritten
    None,
    /// Single entry overwritten
    Single(LogEntry),
    /// Double entry overwritten
    Double(LogEntry, LogEntry),
}

#[derive(Debug)]
pub struct LogEntryRingBuffer<'a> {
    /// The number of items that have been initialized
    len: usize,
    /// The head index where the next write will occupy.
    /// When data is added, the head advances.
    write_at: usize,
    /// The tail index of the oldest entry.
    /// When data is consumed, the tail advances.
    read_from: usize,
    /// Backing storage, provides capacity
    storage: &'a mut [MaybeUninit<LogEntry>],
}

impl<'a> Drop for LogEntryRingBuffer<'a> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<'a> LogEntryRingBuffer<'a> {
    #[inline]
    pub fn from_bytes(bytes: &'a mut [u8]) -> LogEntryRingBuffer<'a> {
        let (_prefix, fixed_slice_vec, _suffix) = LogEntryRingBuffer::align_from_bytes(bytes);
        fixed_slice_vec
    }

    #[inline]
    pub fn align_from_bytes(
        bytes: &'a mut [u8],
    ) -> (&'a mut [u8], LogEntryRingBuffer<'a>, &'a mut [u8]) {
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (
            prefix,
            LogEntryRingBuffer {
                storage,
                len: 0,
                write_at: 0,
                read_from: 0,
            },
            suffix,
        )
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn push_event(&mut self, event_id: EventId) -> OverwrittenEntry {
        self.push_entry(LogEntry::event(event_id))
    }

    #[inline]
    pub fn push_event_with_payload(
        &mut self,
        event_id: EventId,
        payload: u32,
    ) -> (OverwrittenEntry, OverwrittenEntry) {
        let (first, second) = LogEntry::event_with_payload(event_id, payload);
        let first_overwritten = self.push_entry(first);
        let second_overwritten = self.push_entry(second);
        (first_overwritten, second_overwritten)
    }

    #[inline]
    pub fn push_clock(&mut self, clock: LogicalClock) -> (OverwrittenEntry, OverwrittenEntry) {
        let (first, second) = LogEntry::clock(clock);
        let first_overwritten = self.push_entry(first);
        let second_overwritten = self.push_entry(second);
        (first_overwritten, second_overwritten)
    }

    /// Write a single entry to the RingBuffer head (newest)
    #[inline]
    fn push_entry(&mut self, value: LogEntry) -> OverwrittenEntry {
        let overwritten_entry = if (self.len > 0) && (self.write_at == self.read_from) {
            // About to overwrite the tail
            let tail_entry = unsafe { self.storage[self.read_from].as_ptr().read() };
            self.read_from = self.wrap(self.read_from + 1);

            // If the first overwritten entry is a double-word item
            // then read out the second
            if tail_entry.has_clock_bit_set() || tail_entry.has_event_with_payload_bit_set() {
                let next_tail_entry = unsafe { self.storage[self.read_from].as_ptr().read() };
                self.read_from = self.wrap(self.read_from + 1);
                OverwrittenEntry::Double(tail_entry, next_tail_entry)
            } else {
                OverwrittenEntry::Single(tail_entry)
            }
        } else {
            OverwrittenEntry::None
        };

        if self.len < self.capacity() {
            self.len += 1;
        }

        self.storage[self.write_at] = MaybeUninit::new(value);
        self.write_at = self.wrap(self.write_at + 1);

        overwritten_entry
    }

    /// Read a single entry from the RingBuffer tail (oldest)
    #[inline]
    pub fn pop_entry(&mut self) -> Option<LogEntry> {
        if self.is_empty() {
            None
        } else {
            let entry = Some(unsafe { self.storage[self.read_from].as_ptr().read() });
            self.read_from = self.wrap(self.read_from + 1);
            self.len -= 1;
            entry
        }
    }

    /// Read a single entry from the RingBuffer tail (oldest) without advancing
    /// the read cursor
    #[inline]
    pub fn peek_entry(&self) -> Option<LogEntry> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.storage[self.read_from].as_ptr().read() })
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        unsafe {
            (core::slice::from_raw_parts_mut(self.storage.as_mut_ptr() as *mut LogEntry, self.len)
                as *mut [LogEntry])
                .drop_in_place();
        }

        self.len = 0;
        self.write_at = 0;
        self.read_from = 0;
    }

    #[inline]
    fn wrap(&self, index: usize) -> usize {
        index % self.capacity()
    }

    pub(crate) fn as_slice(&self) -> &[LogEntry] {
        unsafe { core::slice::from_raw_parts(self.storage.as_ptr() as *const LogEntry, self.len) }
    }
}

/// An iterator that consumes entries from the tail (oldest) to the head (newest)
impl<'a> Iterator for LogEntryRingBuffer<'a> {
    type Item = LogEntry;

    fn next(&mut self) -> Option<Self::Item> {
        self.pop_entry()
    }
}

impl<'a> From<&'a mut [MaybeUninit<LogEntry>]> for LogEntryRingBuffer<'a> {
    #[inline]
    fn from(v: &'a mut [MaybeUninit<LogEntry>]) -> Self {
        LogEntryRingBuffer {
            storage: v,
            len: 0,
            write_at: 0,
            read_from: 0,
        }
    }
}

impl<'a> From<&'a mut [LogEntry]> for LogEntryRingBuffer<'a> {
    #[inline]
    fn from(v: &'a mut [LogEntry]) -> Self {
        let len = v.len();
        LogEntryRingBuffer {
            storage: unsafe {
                core::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut MaybeUninit<LogEntry>, len)
            },
            len,
            write_at: 0,
            read_from: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        log::{CLOCK_MASK, EVENT_WITH_PAYLOAD_MASK},
        ProbeId,
    };

    impl<'a> LogEntryRingBuffer<'a> {
        #[inline]
        pub fn is_full(&self) -> bool {
            self.len == self.capacity()
        }
    }

    fn entry(raw: u32) -> LogEntry {
        assert_ne!(raw, 0);
        unsafe { LogEntry::new_unchecked(raw) }
    }

    #[test]
    fn happy_path_from_bytes() {
        let mut data = [0u8; 31];
        let mut rb: LogEntryRingBuffer = LogEntryRingBuffer::from_bytes(&mut data[..]);
        assert!(rb.is_empty());
        assert_ne!(rb.capacity(), 0);
        for i in 0..rb.capacity() {
            assert_eq!(rb.push_entry(entry(i as u32 + 1)), OverwrittenEntry::None);
        }
        assert!(rb.is_full());

        rb.clear();
        assert!(!rb.is_full());
        assert_eq!(rb.len, 0);
        assert_eq!(rb.read_from, 0);
        assert_eq!(rb.write_at, 0);
    }

    #[test]
    fn head_overwrites_tail() {
        let mut data = [0u8; 4 * 4]; // 4 u32's
        let mut rb: LogEntryRingBuffer = LogEntryRingBuffer::from_bytes(&mut data[..]);
        assert!(rb.is_empty());
        assert!(!rb.is_full());
        assert_eq!(rb.capacity(), 4);

        assert_eq!(rb.push_entry(entry(1)), OverwrittenEntry::None);
        assert_eq!(rb.push_entry(entry(2)), OverwrittenEntry::None);
        assert_eq!(rb.len(), 2);
        assert_eq!(rb.as_slice(), [entry(1), entry(2)]);

        assert_eq!(rb.push_entry(entry(3)), OverwrittenEntry::None);
        assert_eq!(rb.push_entry(entry(4)), OverwrittenEntry::None);
        assert_eq!(rb.len(), 4);
        assert_eq!(rb.as_slice(), [entry(1), entry(2), entry(3), entry(4)]);

        // Next two single-item entries overwrite the oldest two single-item entries
        assert_eq!(
            rb.push_event(EventId::new(5).unwrap()),
            OverwrittenEntry::Single(entry(1))
        );
        assert_eq!(rb.push_entry(entry(6)), OverwrittenEntry::Single(entry(2)));
        assert_eq!(rb.len(), 4);
        assert_eq!(rb.as_slice(), [entry(5), entry(6), entry(3), entry(4)]);

        // Next double-item entry overwrites the oldest two single-item entries
        let eid = EventId::new(7).unwrap();
        let payload = 8;
        assert_eq!(
            rb.push_event_with_payload(eid, payload),
            (
                OverwrittenEntry::Single(entry(3)),
                OverwrittenEntry::Single(entry(4)),
            )
        );
        assert_eq!(
            rb.as_slice(),
            [
                entry(5),
                entry(6),
                entry(7 | EVENT_WITH_PAYLOAD_MASK),
                entry(8)
            ]
        );

        // Overwrite the next two single-item entries
        assert_eq!(rb.push_entry(entry(9)), OverwrittenEntry::Single(entry(5)));
        assert_eq!(rb.push_entry(entry(10)), OverwrittenEntry::Single(entry(6)));
        assert_eq!(
            rb.as_slice(),
            [
                entry(9),
                entry(10),
                entry(7 | EVENT_WITH_PAYLOAD_MASK),
                entry(8)
            ]
        );

        // Next single-item entry overwrites the oldest double-item entry
        assert_eq!(
            rb.push_entry(entry(11)),
            OverwrittenEntry::Double(entry(7 | EVENT_WITH_PAYLOAD_MASK), entry(8))
        );
        assert_eq!(rb.as_slice(), [entry(9), entry(10), entry(11), entry(8)]);

        // Next double-item overwrites the oldest two single-item entries
        let clock = LogicalClock {
            id: ProbeId::new(12).unwrap(),
            epoch: 0.into(),
            ticks: 13.into(),
        };
        assert_eq!(
            rb.push_clock(clock),
            (OverwrittenEntry::None, OverwrittenEntry::Single(entry(9)))
        );
        assert_eq!(
            rb.as_slice(),
            [entry(13), entry(10), entry(11), entry(12 | CLOCK_MASK)]
        );

        rb.clear();
        assert_eq!(rb.len(), 0);
        assert!(rb.is_empty());
    }

    #[test]
    fn writer_reader() {
        let mut data = [0u8; 4 * 4]; // 4 u32's
        let mut rb: LogEntryRingBuffer = LogEntryRingBuffer::from_bytes(&mut data[..]);
        assert!(rb.is_empty());
        assert!(!rb.is_full());
        assert_eq!(rb.capacity(), 4);

        // Writes advance the head
        assert_eq!(rb.push_entry(entry(1)), OverwrittenEntry::None);
        assert_eq!(rb.push_entry(entry(2)), OverwrittenEntry::None);
        assert_eq!(rb.push_entry(entry(3)), OverwrittenEntry::None);
        assert_eq!(rb.push_entry(entry(4)), OverwrittenEntry::None);
        assert_eq!(rb.as_slice(), [entry(1), entry(2), entry(3), entry(4)]);
        assert!(!rb.is_empty());
        assert!(rb.is_full());

        // Overwrites work
        assert_eq!(rb.push_entry(entry(5)), OverwrittenEntry::Single(entry(1)));
        assert_eq!(rb.as_slice(), [entry(5), entry(2), entry(3), entry(4)]);
        assert!(!rb.is_empty());
        assert!(rb.is_full());

        // Can peek at the current read cursor/tail, does not advance the tail
        assert_eq!(rb.len(), 4);
        assert_eq!(rb.peek_entry(), Some(entry(2)));
        assert_eq!(rb.peek_entry(), Some(entry(2)));
        assert_eq!(rb.peek_entry(), Some(entry(2)));

        // Reads advance the tail
        assert_eq!(rb.len(), 4);
        assert_eq!(rb.peek_entry(), Some(entry(2)));
        assert_eq!(rb.pop_entry(), Some(entry(2)));
        assert_eq!(rb.len(), 3);
        assert_eq!(rb.peek_entry(), Some(entry(3)));
        assert_eq!(rb.pop_entry(), Some(entry(3)));
        assert_eq!(rb.len(), 2);
        assert_eq!(rb.pop_entry(), Some(entry(4)));

        assert_eq!(rb.len(), 1);
        assert_eq!(rb.peek_entry(), Some(entry(5)));
        assert_eq!(rb.peek_entry(), Some(entry(5)));
        assert_eq!(rb.pop_entry(), Some(entry(5)));

        assert_eq!(rb.pop_entry(), None);
        assert_eq!(rb.peek_entry(), None);
        assert!(rb.is_empty());
        assert!(!rb.is_full());
    }

    #[test]
    fn draining_iterator() {
        let mut data = [0u8; 4 * 4]; // 4 u32's
        let mut rb: LogEntryRingBuffer = LogEntryRingBuffer::from_bytes(&mut data[..]);
        assert!(rb.is_empty());
        assert_ne!(rb.capacity(), 0);
        for i in 0..rb.capacity() {
            assert_eq!(rb.push_entry(entry(i as u32 + 1)), OverwrittenEntry::None);
        }
        assert!(rb.is_full());
        assert_eq!(rb.as_slice(), [entry(1), entry(2), entry(3), entry(4)]);

        // Drains from the tail (oldest) to the head (newest)
        let mut index = 0;
        while let Some(e) = rb.next() {
            assert_eq!(e, entry(index + 1));
            index += 1;
        }
    }
}
