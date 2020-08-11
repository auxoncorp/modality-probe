//! The writer of the RaceBuffer, which contains the actual buffer. Entries can be synchronously written and read/iterated
//! from this struct.
use crate::{get_seqn_index, num_missed, Entry};
//use core::iter::Iterator;
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
#[inline]
fn round_to_power_2(length: usize) -> usize {
    let exp: usize = size_of::<usize>() * 8 - (length.leading_zeros() as usize) - 1;
    1 << exp
}

/// An entry or double entry that has just been overwritten
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum WholeEntry<E>
where
    E: Entry,
{
    /// Single entry overwritten
    Single(E),
    /// Double entry overwritten
    Double(E, E),
}

impl<E> WholeEntry<E>
where
    E: Entry,
{
    fn size(&self) -> u64 {
        match self {
            Self::Single(_) => 1,
            _ => 2,
        }
    }
}

#[derive(Debug)]
#[repr(C)]
/// Struct used to write to buffer
pub struct RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Sequence number of the next entry to be written
    write_seqn: u64,
    /// Sequence number of the next entry to be overwritten
    overwrite_seqn: u64,
    /// Backing storage
    storage: &'a mut [MaybeUninit<E>],
    /// Sequence number of next entry to be read from buffer
    /// Note: when using RaceReader, this field is not used
    read_seqn: u64,
    /// Indicates if backing storage should be truncated to a power of 2 length
    /// in order to use optimized indexing
    use_base_2_indexing: bool,
}

impl<'a, E> RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Create new RaceBuffer. Returns error if storage size is not power of 2
    pub fn new(
        storage: &'a mut [MaybeUninit<E>],
        use_base_2_indexing: bool,
    ) -> Result<RaceBuffer<'a, E>, SizeError> {
        if storage.len() < MIN_STORAGE_CAP {
            return Err(SizeError);
        }
        let truncated_len = if use_base_2_indexing {
            round_to_power_2(storage.len())
        } else {
            storage.len()
        };
        Ok(RaceBuffer {
            write_seqn: 0,
            overwrite_seqn: 0,
            storage: &mut storage[..truncated_len],
            read_seqn: 0,
            use_base_2_indexing,
        })
    }

    /// Create new RaceBuffer with properly aligned backing storage
    #[inline]
    pub fn new_from_bytes(
        bytes: &'a mut [u8],
        use_base_2_indexing: bool,
    ) -> Result<RaceBuffer<'a, E>, SizeError> {
        let (_prefix, buf, _suffix) = Self::align_from_bytes(bytes, use_base_2_indexing);
        buf
    }

    /// Create new RaceBuffer with properly aligned backing storage, return unused bytes
    #[inline]
    pub fn align_from_bytes(
        bytes: &'a mut [u8],
        use_base_2_indexing: bool,
    ) -> (
        &'a mut [u8],
        Result<RaceBuffer<'a, E>, SizeError>,
        &'a mut [u8],
    ) {
        // Safe because storage is treated as uninit after transmutation
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (
            prefix,
            RaceBuffer::new(storage, use_base_2_indexing),
            suffix,
        )
    }

    /// Get value of backing storage corresponding at index corresponding to given sequence number
    #[inline]
    pub(crate) unsafe fn read_storage(&self, seqn: u64) -> E {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)].assume_init()
    }

    /// Read entry at given sequence number
    /// Returns None if entry has not been written yet
    /// Note: read_seqn should not point at a double-entry suffix
    fn read_at(&self, read_seqn: u64) -> Option<WholeEntry<E>> {
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
    fn write_to_storage(&mut self, seqn: u64, entry: E) {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)] =
            MaybeUninit::new(entry);
    }

    /// Write single entry to buffer
    pub fn push(&mut self, entry: E) -> Option<WholeEntry<E>> {
        // Overwrite when write sequence number is 1 buffer capacity ahead of overwrite sequence number.
        let overwritten = if self.write_seqn == self.overwrite_seqn + self.capacity() as u64 {
            // Reading storage directly in front of overwrite sequence number is safe because write cursor is ahead of
            // that entry, and the overwrite sequence number is behind it
            let overwritten = self.read_at(self.overwrite_seqn).unwrap();
            self.overwrite_seqn += overwritten.size();
            // Prevent writes from getting reordered
            fence(Ordering::Release);
            Some(overwritten)
        } else {
            None
        };
        self.write_to_storage(self.write_seqn, entry);
        // Prevent writes from getting reordered
        fence(Ordering::Release);
        self.write_seqn += 1;
        // Prevent writes from getting reordered
        fence(Ordering::Release);
        overwritten
    }

    /// Write double entry in single borrow, returning overwritten entry
    pub fn push_double(
        &mut self,
        prefix: E,
        suffix: E,
    ) -> (Option<WholeEntry<E>>, Option<WholeEntry<E>>) {
        let first_overwritten = self.push(prefix);
        let second_overwritten = self.push(suffix);
        (first_overwritten, second_overwritten)
    }

    /// Return number of items missed between tail and oldest entry present in the buffer, or 0 if tail is currently present
    pub fn num_missed(&self) -> u64 {
        num_missed(self.read_seqn, self.overwrite_seqn)
    }

    /// Read the entry at tail, or the oldest entry present in the buffer if tail has already been overwritten.
    /// Returns None if the tail is caught up to the head
    pub fn peek(&self) -> Option<WholeEntry<E>> {
        if self.read_seqn == self.write_seqn {
            None
        } else {
            // Read at read_seqn unless already overwritten
            let next_seqn = u64::max(self.read_seqn, self.overwrite_seqn);
            self.read_at(next_seqn)
        }
    }

    /// Read the entry at tail, or the oldest entry present in the buffer if tail has already been overwritten, move
    /// the tail to point to the entry after the one that was popped.
    /// Returns None if the tail is caught up to the head
    pub fn pop(&mut self) -> Option<WholeEntry<E>> {
        let tail = self.peek();
        let increment = if let Some(entry) = tail {
            entry.size()
        } else {
            0
        };
        self.read_seqn = u64::max(self.read_seqn + increment, self.overwrite_seqn + increment);
        tail
    }

    /// Create iterator over the entries currently present in the buffer without changing the tail
    #[inline]
    pub fn iter_peek<'b>(&'b mut self) -> RaceBufferIter<'a, 'b, E> {
        let start_seqn = u64::max(self.read_seqn, self.overwrite_seqn);
        RaceBufferIter::new(self, start_seqn)
    }

    /// Get two slices which together represent the entries currently present in the buffer, where the second
    /// slice comes directly after the first
    pub fn get_linear_slices(&self) -> (&[E], &[E]) {
        let overwrite_seqn_index = get_seqn_index(
            self.capacity(),
            self.overwrite_seqn,
            self.use_base_2_indexing,
        );
        let write_seqn_index =
            get_seqn_index(self.capacity(), self.write_seqn, self.use_base_2_indexing);
        // Safe to assume entries in front of overwrite sequence number and behind write sequence number are initialized
        if overwrite_seqn_index >= write_seqn_index
            && (self.overwrite_seqn != 0 || self.write_seqn != 0)
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

    /// Get the number of items currently in the buffer which have not been read yet
    pub fn len(&self) -> usize {
        let start_seqn = self.read_seqn.max(self.overwrite_seqn);
        (self.write_seqn - start_seqn) as usize
    }

    /// Return true if there are no items to read
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    pub(crate) fn get_write_seqn(&self) -> u64 {
        self.write_seqn
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    pub(crate) fn get_overwrite_seqn(&self) -> u64 {
        self.overwrite_seqn
    }
}

impl<E> Iterator for RaceBuffer<'_, E>
where
    E: Entry,
{
    type Item = WholeEntry<E>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

/// Iteratates through a RaceBuffer
pub struct RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    /// Target RaceBuffer
    buffer: &'b RaceBuffer<'a, E>,
    /// Sequence number of next entry to read
    read_seqn: u64,
}

impl<'a, 'b, E> RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    /// Create a new iterator over the RaceBuffer at the given starting sequence number
    pub fn new(buffer: &'b RaceBuffer<'a, E>, start_seqn: u64) -> Self {
        Self {
            buffer,
            read_seqn: start_seqn,
        }
    }
}

impl<'a, 'b, E> Iterator for RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    type Item = WholeEntry<E>;
    fn next(&mut self) -> Option<WholeEntry<E>> {
        let tail = self.buffer.read_at(self.read_seqn);
        if let Some(entry) = tail {
            self.read_seqn += entry.size();
        }
        tail
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::OrderedEntry;
    use core::mem::MaybeUninit;

    /// Test backing storage size rounding and minimum size enforcement
    #[test]
    fn test_init_sizes() {
        // Ensure minimum storage size is checked
        for i in 0..MIN_STORAGE_CAP {
            let mut too_small_storage = vec![MaybeUninit::<OrderedEntry>::uninit(); i];
            assert!(RaceBuffer::new(&mut too_small_storage[..], false).is_err());
            assert!(RaceBuffer::new(&mut too_small_storage[..], true).is_err());
        }

        let input_sizes = [4, 5, 6, 7, 8, 9, 12, 16];

        let output_sizes: Vec<usize> = input_sizes
            .iter()
            .map(|size| {
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); *size];
                RaceBuffer::new(&mut storage[..], false)
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
                RaceBuffer::new(&mut storage[..], true)
                    .unwrap()
                    .get_slice()
                    .len()
            })
            .collect();
        assert_eq!(&[4, 4, 4, 4, 8, 8, 8, 16][..], &rounded_output_sizes[..]);
    }

    #[test]
    fn test_from_bytes() {
        const STORAGE_CAP: usize = 16;
        let mut storage = [0u8; STORAGE_CAP * size_of::<OrderedEntry>()];
        let buf = RaceBuffer::<OrderedEntry>::new_from_bytes(&mut storage[..], false).unwrap();
        // Should not lose more than one entry
        assert!(buf.capacity() == 16 || buf.capacity() == 15)
    }

    #[test]
    fn test_read_at() {
        const STORAGE_CAP: usize = 8;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();

        for i in 0..16 {
            // None written yet
            assert_eq!(buf.read_at(i), None);
        }
        for i in 0..16 {
            buf.push(OrderedEntry::from_index(i));
        }
        for i in 0..8 {
            // First 8 overwritten
            assert_eq!(buf.read_at(i), None);
        }
        for i in 8..16 {
            assert_eq!(
                buf.read_at(i),
                Some(WholeEntry::Single(OrderedEntry::from_index(i as u32)))
            );
        }
        for i in 16..32 {
            // Not written yet
            assert_eq!(buf.read_at(i), None);
        }
    }

    #[test]
    fn test_pushing_popping_num_missed() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();

        // None written yet
        assert_eq!(buf.peek(), None);
        assert_eq!(buf.pop(), None);

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
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();

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
        // Push 3 entries, meaning only first entry of above double has new entry written over it
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
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
        for i in 0..6 {
            buf.push(OrderedEntry::from_index(i));
        }
        buf.push_double(
            OrderedEntry::from_index_prefix(6),
            OrderedEntry::from_index_prefix(7),
        );

        assert_eq!(buf.num_missed(), 4);
        assert_eq!(
            buf.iter_peek().collect::<Vec<WholeEntry<OrderedEntry>>>(),
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

        let mut out = Vec::new();
        for entry in &mut buf {
            out.push(entry);
        }
        assert_eq!(
            out,
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
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
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
}
