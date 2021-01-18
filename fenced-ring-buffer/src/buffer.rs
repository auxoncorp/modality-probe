//! The writer of the FencedRingBuffer, which contains the actual buffer.
//! Entries can be synchronously written and read/iterated from this struct.
use crate::{get_seqn_index, num_missed, Entry, SeqNum, WholeEntry};
use core::cmp::max;
use core::fmt;
use core::mem::size_of;
use core::mem::MaybeUninit;
use core::sync::atomic::fence;
use core::sync::atomic::Ordering;

/// Minimum allowed capacity of backing storage
pub const MIN_STORAGE_CAP: usize = 4;

/// Error for given storage size that is too small
pub struct SizeError;

impl fmt::Debug for SizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Storage capacity must be at least {}", MIN_STORAGE_CAP,)
    }
}

/// Round given length down to a power of 2
///
/// Note: the given length must be at least 1
#[inline]
fn round_to_power_2(length: usize) -> usize {
    debug_assert!(length > 0);
    let exp: usize = size_of::<usize>() * 8 - (length.leading_zeros() as usize) - 1;
    1 << exp
}

#[derive(Debug)]
#[repr(C)]
/// Struct used to write to buffer
pub struct FencedRingBuffer<'a, E>
where
    E: Entry,
{
    /// Sequence number of the next entry to be written
    pub write_seqn: SeqNum,
    /// Sequence number of the next entry to be overwritten
    pub overwrite_seqn: SeqNum,
    /// Backing storage
    pub storage: &'a mut [MaybeUninit<E>],
    /// Sequence number of next entry to be read from buffer
    /// Note: when using FencedReader, this field is not used
    read_seqn: SeqNum,
    /// Indicates if backing storage should be truncated to a power of 2 length
    /// in order to use optimized indexing
    use_base_2_indexing: bool,
}

impl<'a, E> FencedRingBuffer<'a, E>
where
    E: Entry,
{
    /// Create new FencedRingBuffer. Returns error if storage capacity is
    /// smaller than the minimum size
    pub fn new(
        storage: &'a mut [MaybeUninit<E>],
        use_base_2_indexing: bool,
    ) -> Result<FencedRingBuffer<'a, E>, SizeError> {
        if storage.len() < MIN_STORAGE_CAP {
            return Err(SizeError);
        }
        let truncated_len = if use_base_2_indexing {
            round_to_power_2(storage.len())
        } else {
            storage.len()
        };
        Ok(FencedRingBuffer {
            write_seqn: SeqNum::new(0, 0),
            overwrite_seqn: SeqNum::new(0, 0),
            storage: &mut storage[..truncated_len],
            read_seqn: SeqNum::new(0, 0),
            use_base_2_indexing,
        })
    }

    /// Create new FencedRingBuffer with properly aligned backing storage
    #[inline]
    pub fn new_from_uninit_bytes(
        bytes: &'a mut [MaybeUninit<u8>],
        use_base_2_indexing: bool,
    ) -> Result<FencedRingBuffer<'a, E>, SizeError> {
        let (_prefix, buf, _suffix) = Self::align_from_uninit_bytes(bytes, use_base_2_indexing);
        buf
    }

    /// Create new FencedRingBuffer with properly aligned backing storage,
    /// return unused bytes
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn align_from_uninit_bytes(
        bytes: &'a mut [MaybeUninit<u8>],
        use_base_2_indexing: bool,
    ) -> (
        &'a mut [MaybeUninit<u8>],
        Result<FencedRingBuffer<'a, E>, SizeError>,
        &'a mut [MaybeUninit<u8>],
    ) {
        // Safe because storage is treated as uninit after transmutation
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (
            prefix,
            FencedRingBuffer::new(storage, use_base_2_indexing),
            suffix,
        )
    }

    /// Get value of backing storage corresponding at index corresponding to
    /// given sequence number
    #[inline]
    pub(crate) unsafe fn read_storage(&self, seqn: SeqNum) -> E {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)].assume_init()
    }

    /// Read entry at given sequence number
    /// Returns None if entry has not been written yet
    /// Note: read_seqn should not point at a double-entry suffix
    fn read_at(&self, read_seqn: SeqNum) -> Option<WholeEntry<E>> {
        if read_seqn < self.overwrite_seqn || read_seqn >= self.write_seqn {
            None
        } else {
            // Safe to read because read seq num is between overwrite and write seq nums
            let first_entry = unsafe { self.read_storage(read_seqn) };
            if first_entry.is_prefix() {
                debug_assert!(read_seqn <= self.write_seqn - 2);
                // Safe because if prefix is present, suffix will also be present
                let second_entry = unsafe { self.read_storage(read_seqn + 1) };
                Some(WholeEntry::Double(first_entry, second_entry))
            } else {
                Some(WholeEntry::Single(first_entry))
            }
        }
    }

    /// Write to storage at index corresponding to given sequence number
    #[inline]
    fn write_to_storage(&mut self, seqn: SeqNum, entry: E) {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)] =
            MaybeUninit::new(entry);
    }

    /// Write single entry to buffer
    pub fn push(&mut self, entry: E) -> Option<WholeEntry<E>> {
        // Overwrite when write sequence number is 1 buffer capacity ahead of overwrite
        // sequence number.
        let possible_overwritten =
            if self.write_seqn == self.overwrite_seqn + self.capacity() as u64 {
                // Reading storage directly in front of overwrite sequence number is safe
                // because write cursor is ahead of that entry, and the
                // overwrite sequence number is behind it
                let overwritten = self.read_at(self.overwrite_seqn).unwrap();
                self.overwrite_seqn
                    .increment((overwritten.size() as u64).into());
                // Prevent writes from getting reordered
                Some(overwritten)
            } else {
                None
            };
        self.write_to_storage(self.write_seqn, entry);
        // Prevent writes from getting reordered
        fence(Ordering::Release);
        self.write_seqn.increment(1.into());
        // Prevent writes from getting reordered
        possible_overwritten
    }

    /// Write double entry in single borrow, returning overwritten entry
    pub fn push_double(
        &mut self,
        prefix: E,
        suffix: E,
    ) -> (Option<WholeEntry<E>>, Option<WholeEntry<E>>) {
        debug_assert!(prefix.is_prefix());
        let first_overwritten = self.push(prefix);
        let second_overwritten = self.push(suffix);
        (first_overwritten, second_overwritten)
    }

    /// Return number of items missed between tail and oldest entry present in
    /// the buffer, or 0 if tail is currently present
    pub fn num_missed(&self) -> u64 {
        num_missed(self.read_seqn, self.overwrite_seqn).into()
    }

    /// Read the entry at tail, or the oldest entry present in the buffer if
    /// tail has already been overwritten. Returns None if the tail is
    /// caught up to the head
    pub fn peek(&self) -> Option<WholeEntry<E>> {
        if self.read_seqn == self.write_seqn {
            None
        } else {
            // Read at read_seqn unless already overwritten
            let next_seqn = max(self.read_seqn, self.overwrite_seqn);
            self.read_at(next_seqn)
        }
    }

    /// Read the ith entry forward from the current read cursor, where
    /// peek_at(0) == peek().
    pub fn peek_at(&self, i: u64) -> Option<WholeEntry<E>> {
        let read_seqn = max(self.read_seqn, self.overwrite_seqn);
        let seqn = read_seqn + i;
        if seqn >= self.write_seqn {
            None
        } else {
            self.read_at(seqn)
        }
    }

    /// Read the entry at tail, or the oldest entry present in the buffer if
    /// tail has already been overwritten, move the tail to point to the
    /// entry after the one that was popped. Returns None if the tail is
    /// caught up to the head
    pub fn pop(&mut self) -> Option<WholeEntry<E>> {
        let tail = self.peek();
        let increment = if let Some(entry) = tail {
            entry.size() as u64
        } else {
            0
        };
        self.read_seqn = max(self.read_seqn + increment, self.overwrite_seqn + increment);
        tail
    }

    /// Create iterator over the entries currently present in the buffer without
    /// changing the tail
    #[inline]
    pub fn iter<'b>(&'b self) -> Iter<'a, 'b, E> {
        let start_seqn = max(self.read_seqn, self.overwrite_seqn);
        Iter::new(self, start_seqn)
    }

    /// Create draining iterator
    #[inline]
    pub fn drain<'b>(&'b mut self) -> Drain<'a, 'b, E> {
        Drain::new(self)
    }

    /// Get two slices which together represent the entries currently present in
    /// the buffer, where the second slice comes directly after the first
    pub fn get_linear_slices(&self) -> (&[E], &[E]) {
        let overwrite_seqn_index = get_seqn_index(
            self.capacity(),
            self.overwrite_seqn,
            self.use_base_2_indexing,
        );
        let write_seqn_index =
            get_seqn_index(self.capacity(), self.write_seqn, self.use_base_2_indexing);
        // Safe to assume entries in front of overwrite sequence number and behind write
        // sequence number are initialized
        if overwrite_seqn_index >= write_seqn_index
            && (u64::from(self.overwrite_seqn) != 0 || u64::from(self.write_seqn) != 0)
        {
            unsafe {
                (
                    &*(&self.storage[overwrite_seqn_index..] as *const [MaybeUninit<E>]
                        as *const [E]),
                    &*(&self.storage[..write_seqn_index] as *const [MaybeUninit<E>]
                        as *const [E]),
                )
            }
        } else {
            // Present entries do not cross end of storage, second slice has 0 length
            unsafe {
                (
                    &*(&self.storage[overwrite_seqn_index..write_seqn_index]
                        as *const [MaybeUninit<E>] as *const [E]),
                    &*(&self.storage[write_seqn_index..write_seqn_index]
                        as *const [MaybeUninit<E>] as *const [E]),
                )
            }
        }
    }

    /// Get the number of items currently in the buffer which have not been read
    /// yet
    pub fn len(&self) -> usize {
        let start_seqn = self.read_seqn.max(self.overwrite_seqn);
        let len: u64 = (self.write_seqn - start_seqn).into();
        len as usize
    }

    /// Return true if there are no items to read
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns true if the buffer is full to capacity.
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Get capacity of buffer storage
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    /// Get underlying storage slice
    #[inline]
    pub fn get_slice(&self) -> &[MaybeUninit<E>] {
        self.storage
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    pub(crate) fn get_write_seqn(&self) -> SeqNum {
        self.write_seqn
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    pub(crate) fn get_overwrite_seqn(&self) -> SeqNum {
        self.overwrite_seqn
    }
}

/// Drains a FencedRingBuffer
pub struct Drain<'a, 'b, E>
where
    E: Entry,
{
    /// Target FencedRingBuffer
    buffer: &'b mut FencedRingBuffer<'a, E>,
}

impl<'a, 'b, E> Drain<'a, 'b, E>
where
    E: Entry,
{
    /// Create a new iterator over the FencedRingBuffer at the given starting
    /// sequence number
    fn new(buffer: &'b mut FencedRingBuffer<'a, E>) -> Self {
        Self { buffer }
    }
}

impl<E> Iterator for Drain<'_, '_, E>
where
    E: Entry,
{
    type Item = WholeEntry<E>;
    fn next(&mut self) -> Option<Self::Item> {
        self.buffer.pop()
    }
}

/// Iterates through a FencedRingBuffer
pub struct Iter<'a, 'b, E>
where
    E: Entry,
{
    /// Target FencedRingBuffer
    buffer: &'b FencedRingBuffer<'a, E>,
    /// Sequence number of next entry to read
    read_seqn: SeqNum,
}

impl<'a, 'b, E> Iter<'a, 'b, E>
where
    E: Entry,
{
    /// Create a new iterator over the FencedRingBuffer at the given starting
    /// sequence number
    fn new(buffer: &'b FencedRingBuffer<'a, E>, start_seqn: SeqNum) -> Self {
        Self {
            buffer,
            read_seqn: start_seqn,
        }
    }
}

impl<'a, 'b, E> Iterator for Iter<'a, 'b, E>
where
    E: Entry,
{
    type Item = WholeEntry<E>;
    fn next(&mut self) -> Option<WholeEntry<E>> {
        let tail = self.buffer.read_at(self.read_seqn);
        if let Some(entry) = tail {
            self.read_seqn += entry.size() as u64;
        }
        tail
    }
}

#[cfg(all(feature = "std", test))]
mod tests {
    use super::*;
    use crate::test_support::OrderedEntry;
    use core::mem::MaybeUninit;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn round_to_power_of_two(num in 1..=usize::MAX) {
            let rounded_num = round_to_power_2(num);
            prop_assert!(rounded_num > 0);
            let mut n = rounded_num;
            while n != 1 {
                prop_assert_eq!(n % 2, 0);
                prop_assert_eq!(n & 1, 0);
                n = n / 2;
            }
        }
    }

    #[test]
    fn entry_helpers() {
        let e = WholeEntry::Single(OrderedEntry::from_index(1));
        assert_eq!(e.size(), 1);
        assert_eq!(e.first_entry(), &OrderedEntry::from_index(1));
        assert_eq!(e.is_double(), false);
        let e = WholeEntry::Double(OrderedEntry::from_index(2), OrderedEntry::from_index(3));
        assert_eq!(e.size(), 2);
        assert_eq!(e.first_entry(), &OrderedEntry::from_index(2));
        assert_eq!(e.is_double(), true);
    }

    /// Test backing storage size rounding and minimum size enforcement
    #[test]
    fn test_init_sizes() {
        // Ensure minimum storage size is checked
        for i in 0..MIN_STORAGE_CAP {
            let mut too_small_storage = vec![MaybeUninit::<OrderedEntry>::uninit(); i];
            assert!(FencedRingBuffer::new(&mut too_small_storage[..], false).is_err());
            assert!(FencedRingBuffer::new(&mut too_small_storage[..], true).is_err());
        }

        let input_sizes = [4, 5, 6, 7, 8, 9, 12, 16];

        let output_sizes: Vec<usize> = input_sizes
            .iter()
            .map(|size| {
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); *size];
                FencedRingBuffer::new(&mut storage[..], false)
                    .unwrap()
                    .get_slice()
                    .len()
            })
            .collect();
        assert_eq!(&input_sizes[..], &output_sizes[..]);

        let rounded_output_sizes: Vec<usize> = input_sizes
            .iter()
            .map(|size| {
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); *size];
                FencedRingBuffer::new(&mut storage[..], true)
                    .unwrap()
                    .get_slice()
                    .len()
            })
            .collect();
        assert_eq!(&[4, 4, 4, 4, 8, 8, 8, 16][..], &rounded_output_sizes[..]);

        proptest!(
            ProptestConfig::default(),
            |(size in MIN_STORAGE_CAP..=3333)| {
                let use_power_of_2 = false;
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); size];
                let len = FencedRingBuffer::new(&mut storage[..], use_power_of_2)
                    .unwrap()
                    .get_slice()
                    .len();
                prop_assert_eq!(size, len);

                let use_power_of_2 = true;
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); size];
                let len = FencedRingBuffer::new(&mut storage[..], use_power_of_2)
                    .unwrap()
                    .get_slice()
                    .len();
                prop_assert_eq!(round_to_power_2(size), len);
            }
        );
    }

    proptest! {
        #[test]
        fn test_from_bytes(storage_cap in MIN_STORAGE_CAP..=7777) {
            let mut storage = vec![MaybeUninit::new(0u8); storage_cap * size_of::<OrderedEntry>()];
            let buf =
                FencedRingBuffer::<OrderedEntry>::new_from_uninit_bytes(&mut storage[..], false).unwrap();
            // Should not lose more than one entry
            prop_assert!(buf.capacity() == storage_cap || (buf.capacity() == storage_cap - 1))
        }
    }

    proptest! {
        #[test]
        fn test_read_at(base_storage_cap in MIN_STORAGE_CAP..=8192) {
            let cap = round_to_power_2(base_storage_cap) as u64;
            let cap_2x = cap * 2;
            let cap_4x = cap * 4;
            let mut storage = vec![MaybeUninit::uninit(); cap as usize];
            let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();

            for i in 0..cap_2x {
                // None written yet
                assert_eq!(buf.read_at(i.into()), None);
            }
            for i in 0..cap_2x {
                buf.push(OrderedEntry::from_index(i as u32));
            }
            for i in 0..cap {
                // First N overwritten
                assert_eq!(buf.read_at(i.into()), None);
            }
            for i in cap..cap_2x {
                assert_eq!(
                    buf.read_at(i.into()),
                    Some(WholeEntry::Single(OrderedEntry::from_index(i as u32)))
                );
            }
            for i in cap_2x..cap_4x {
                // Not written yet
                assert_eq!(buf.read_at(i.into()), None);
            }
        }
    }

    #[test]
    fn test_pushing_popping_num_missed() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();

        // None written yet
        assert_eq!(buf.peek(), None);
        assert_eq!(buf.pop(), None);
        assert!(!buf.is_full());
        assert!(buf.is_empty());

        for i in 0..2 {
            buf.push(OrderedEntry::from_index(i));
        }
        // Peek should not modify tail
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Single(OrderedEntry::from_index(0)))
        );
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Single(OrderedEntry::from_index(0)))
        );
        // Pop should increment tail
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Single(OrderedEntry::from_index(0)))
        );
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Single(OrderedEntry::from_index(1)))
        );

        for i in 2..8 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert!(buf.is_full());
        assert!(!buf.is_empty());
        // Buffer holds 4, 6 were written past tail
        assert_eq!(buf.num_missed(), 2);
        // Peek should use oldest if tail overwritten
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Single(OrderedEntry::from_index(4)))
        );
        // Peek does not modify tail
        assert_eq!(buf.num_missed(), 2);
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Single(OrderedEntry::from_index(4)))
        );
        // Pop fast forwards tail
        assert_eq!(buf.num_missed(), 0);
        for i in 5..8 {
            assert_eq!(
                buf.pop(),
                Some(WholeEntry::Single(OrderedEntry::from_index(i)))
            );
        }
    }

    #[test]
    fn test_double_entries() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();

        // Should be able to push, peek, and pop like a single entry
        buf.push_double(
            OrderedEntry::from_index_prefix(0),
            OrderedEntry::from_index_suffix(1),
        );
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Double(
                OrderedEntry::from_index_prefix(0),
                OrderedEntry::from_index_suffix(1)
            ))
        );
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Double(
                OrderedEntry::from_index_prefix(0),
                OrderedEntry::from_index_suffix(1)
            ))
        );
        assert_eq!(buf.pop(), None);

        buf.push_double(
            OrderedEntry::from_index_prefix(2),
            OrderedEntry::from_index_suffix(3),
        );
        // Push 3 entries, meaning only first entry of above double has new entry
        // written over it
        buf.push_double(
            OrderedEntry::from_index_prefix(4),
            OrderedEntry::from_index_suffix(5),
        );
        buf.push(OrderedEntry::from_index(6));
        // Whole double should be considered missed
        assert_eq!(buf.num_missed(), 2);
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Double(
                OrderedEntry::from_index_prefix(4),
                OrderedEntry::from_index_suffix(5),
            ))
        );

        // Overwrite the prefix of a double with the suffix of a double
        buf.push_double(
            OrderedEntry::from_index_prefix(7),
            OrderedEntry::from_index_suffix(8),
        );
        // Whole double should be considered missed
        assert_eq!(buf.num_missed(), 4);
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Single(OrderedEntry::from_index(6)))
        );
        assert_eq!(
            buf.pop(),
            Some(WholeEntry::Double(
                OrderedEntry::from_index_prefix(7),
                OrderedEntry::from_index_suffix(8),
            ))
        );
        assert_eq!(buf.pop(), None);
    }

    #[test]
    fn test_iteration() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();
        for i in 0..6 {
            buf.push(OrderedEntry::from_index(i));
        }
        buf.push_double(
            OrderedEntry::from_index_prefix(6),
            OrderedEntry::from_index_prefix(7),
        );

        assert_eq!(buf.num_missed(), 4);
        assert_eq!(
            buf.iter().collect::<Vec<WholeEntry<OrderedEntry>>>(),
            vec![
                WholeEntry::Single(OrderedEntry::from_index(4)),
                WholeEntry::Single(OrderedEntry::from_index(5)),
                WholeEntry::Double(
                    OrderedEntry::from_index_prefix(6),
                    OrderedEntry::from_index_prefix(7)
                )
            ]
        );

        // iter_peek() peek does not modify tail
        assert_eq!(buf.num_missed(), 4);
        assert_eq!(
            buf.peek(),
            Some(WholeEntry::Single(OrderedEntry::from_index(4)))
        );

        assert_eq!(
            buf.drain().collect::<Vec<WholeEntry<OrderedEntry>>>(),
            vec![
                WholeEntry::Single(OrderedEntry::from_index(4)),
                WholeEntry::Single(OrderedEntry::from_index(5)),
                WholeEntry::Double(
                    OrderedEntry::from_index_prefix(6),
                    OrderedEntry::from_index_prefix(7)
                )
            ]
        );
        // iterating through buffer moves tail
        assert_eq!(buf.num_missed(), 0);
        assert_eq!(buf.peek(), None);
    }

    #[test]
    fn test_get_linear_slices() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();
        assert_eq!(buf.get_linear_slices(), (&[][..], &[][..]));
        for i in 0..2 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(
            buf.get_linear_slices(),
            (
                &[OrderedEntry::from_index(0), OrderedEntry::from_index(1)][..],
                &[][..]
            )
        );
        for i in 2..6 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(
            buf.get_linear_slices(),
            (
                &[OrderedEntry::from_index(2), OrderedEntry::from_index(3)][..],
                &[OrderedEntry::from_index(4), OrderedEntry::from_index(5)][..]
            )
        );
        for i in 6..8 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(
            buf.get_linear_slices(),
            (
                &[
                    OrderedEntry::from_index(4),
                    OrderedEntry::from_index(5),
                    OrderedEntry::from_index(6),
                    OrderedEntry::from_index(7)
                ][..],
                &[][..]
            )
        );
    }

    proptest! {
        #[test]
        fn missed_entries_are_accounted_for(
            single_entry_overflows in 1_usize..=64_usize,
            double_entry_overflows in 1_usize..=64_usize,
        ) {
            let storage_cap = 1 + single_entry_overflows + (2 * double_entry_overflows);

            let mut storage = vec![MaybeUninit::uninit(); storage_cap];
            let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();
            prop_assert_eq!(buf.capacity(), storage_cap);
            prop_assert_eq!(buf.is_empty(), true);

            // Fills to capacity
            for i in 0..storage_cap {
                buf.push(OrderedEntry::from_index(i as _));
            }
            prop_assert_eq!(buf.num_missed(), 0);
            prop_assert_eq!(buf.is_empty(), false);
            prop_assert_eq!(buf.len(), storage_cap);

            // Overflowing single entries accounted for
            for i in 0..single_entry_overflows {
                buf.push(OrderedEntry::from_index(i as _));
            }
            prop_assert_eq!(buf.num_missed(), single_entry_overflows as u64);
            prop_assert_eq!(buf.is_empty(), false);
            prop_assert_eq!(buf.len(), storage_cap);

            for i in 0..double_entry_overflows {
                buf.push_double(
                    OrderedEntry::from_index_prefix(i as _),
                    OrderedEntry::from_index_prefix((i + 1) as _),
                );
            }
            prop_assert_eq!(
                buf.num_missed(),
                (single_entry_overflows + (2 * double_entry_overflows)) as u64
            );
            prop_assert_eq!(buf.is_empty(), false);
            prop_assert_eq!(buf.len(), storage_cap);
        }
    }
}
