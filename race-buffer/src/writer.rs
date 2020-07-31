//! The writer of the RaceBuffer, which contains the actual buffer. Entries can be synchronously written and read/iterated
//! from this struct.
use crate::{get_seqn_index, get_seqn_mod, num_missed, seqn_add, Entry, SEQN_MOD_MAX, PossiblyMissed};
use core::iter::Iterator;
use core::mem::size_of;
use core::mem::transmute;
use core::mem::MaybeUninit;
use core::sync::atomic::fence;
use core::sync::atomic::Ordering;

#[cfg(not(feature = "std"))]
use core::fmt;
#[cfg(feature = "std")]
use std::fmt;

/// Minimum allowed capacity of backing storage
pub const MIN_STORAGE_CAP: usize = 4;
/// Error for given storage size that is too small
pub struct SizeError;

impl fmt::Debug for SizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Storage capacity must be at least {} but no greater than {}.",
            MIN_STORAGE_CAP,
            SEQN_MOD_MAX / 2,
        )
    }
}

#[inline]
/// Round given length down to a power of 2
fn round_to_power_2(length: usize) -> usize {
    let exp: usize = size_of::<usize>() * 8 - (length.leading_zeros() as usize) - 1;
    1 << exp
}

/// An entry or double entry that has just been overwritten
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum OverwrittenEntry<E>
where
    E: Entry,
{
    /// No entry overwritten
    None,
    /// Single entry overwritten
    Single(E),
    /// Double entry overwritten
    Double(E, E),
}

#[derive(Debug)]
#[repr(C)]
/// Struct used to write to buffer
pub struct RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Sequence number of the next entry to be written
    write_seqn: u32,
    /// Sequence number of the next entry to be overwritten
    overwrite_seqn: u32,
    /// Backing storage
    storage: &'a mut [MaybeUninit<E>],
    /// Sequence number modulus for wrapping to 0
    seqn_mod: u32,
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
        let truncated_len = if use_base_2_indexing {
            round_to_power_2(storage.len())
        } else {
            storage.len()
        };
        // Storage size must be greater than the minimum size, but less than the maximum
        // sequence number modulus. This is to ensure that the modulus is at least twice
        // the buffer capacity.
        // Note: this is required because if the sequence number modulus was equal to the buffer capacity,
        // then the overwrite cursor would not be incremented until the write cursor had already wrapped the entire modulus,
        // causing the overwrite cursor to remain 0 forever
        if truncated_len < MIN_STORAGE_CAP || truncated_len > (SEQN_MOD_MAX / 2) as usize {
            Err(SizeError)
        } else {
            Ok(RaceBuffer {
                write_seqn: 0,
                overwrite_seqn: 0,
                storage: &mut storage[..truncated_len],
                seqn_mod: get_seqn_mod(truncated_len as u32),
                use_base_2_indexing,
            })
        }
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

    /// Get value of backing storage corresponding to given index
    #[inline]
    pub(crate) unsafe fn read_storage(&self, seqn: u32) -> E {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)].assume_init()
    }

    #[inline]
    fn write_to_storage(&mut self, seqn: u32, entry: E) {
        self.storage[get_seqn_index(self.capacity(), seqn, self.use_base_2_indexing)] =
            MaybeUninit::new(entry);
    }

    /// Write single entry to buffer
    pub fn write(&mut self, entry: E) -> OverwrittenEntry<E> {
        let overwritten;
        // Overwrite when write sequence number is 1 buffer capacity ahead of overwrite sequence number
        if self.write_seqn == seqn_add(self.overwrite_seqn, self.capacity() as u32, self.seqn_mod) {
            if unsafe { self.read_storage(self.write_seqn).is_prefix() } {
                // Reading storage is safe because buffer has already looped once
                overwritten = unsafe {
                    OverwrittenEntry::Double(
                        self.read_storage(self.overwrite_seqn),
                        self.read_storage(seqn_add(self.overwrite_seqn, 1, self.seqn_mod)),
                    )
                };
                // If overwriting double, increment overwrite sequence number by 2
                self.overwrite_seqn = seqn_add(self.overwrite_seqn, 2, self.seqn_mod);
                // Prevent writes from getting reordered
                fence(Ordering::Release);
            } else {
                // Reading storage is safe because buffer has already looped once
                overwritten =
                    unsafe { OverwrittenEntry::Single(self.read_storage(self.overwrite_seqn)) };
                self.overwrite_seqn = seqn_add(self.overwrite_seqn, 1, self.seqn_mod);
                // Prevent writes from getting reordered
                fence(Ordering::Release);
            }
        } else {
            overwritten = OverwrittenEntry::None;
        }
        self.write_to_storage(self.write_seqn, entry);
        // Prevent writes from getting reordered
        fence(Ordering::Release);
        self.write_seqn = seqn_add(self.write_seqn, 1, self.seqn_mod);
        // Prevent writes from getting reordered
        fence(Ordering::Release);
        overwritten
    }

    /// Write double entry in single borrow, returning overwritten entry
    pub fn write_double(
        &mut self,
        prefix: E,
        suffix: E,
    ) -> (OverwrittenEntry<E>, OverwrittenEntry<E>) {
        let first_overwritten = self.write(prefix);
        let second_overwritten = self.write(suffix);
        (first_overwritten, second_overwritten)
    }

    /// Read entry at given sequence number. Entry may or may not currently be present in the buffer.
    #[inline]
    pub fn read(&self, mut read_seqn: u32) -> PossiblyMissed<E> {
        if read_seqn >= self.get_seqn_mod() {
            read_seqn = read_seqn % self.get_seqn_mod();
        }
        let num_missed = num_missed(
            read_seqn,
            self.overwrite_seqn,
            self.write_seqn,
            self.seqn_mod,
        );
        // If num_missed is greater than zero, entry is not present. If the read sequence number is caught
        // up to the write seqn, then the next entry has not been written yet
        if num_missed == 0 && read_seqn != self.write_seqn {
            PossiblyMissed::Entry(unsafe { self.read_storage(read_seqn) })
        } else {
            PossiblyMissed::Missed
        }
    }

    /// Iterate over the entries, where None represents a missed entry
    #[inline]
    pub fn iter<'b>(&'b self, start_seqn: u32) -> RaceBufferIter<'a, 'b, E> {
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
                    transmute(&self.storage[overwrite_seqn_index..]),
                    transmute(&self.storage[..write_seqn_index]),
                )
            }
        } else {
            // Present entries do not cross end of storage, second slice has 0 length
            unsafe {
                (
                    transmute(&self.storage[overwrite_seqn_index..write_seqn_index]),
                    transmute(&self.storage[write_seqn_index..write_seqn_index]),
                )
            }
        }
    }

    /// Get underlying storage slice
    #[inline]
    pub fn get_slice(&self) -> &[MaybeUninit<E>] {
        self.storage
    }

    /// Get capacity of buffer
    #[inline]
    pub fn capacity(&self) -> u32 {
        // Must be less than u32::MAX
        self.storage.len() as u32
    }

    /// Get current value of write sequence number
    #[inline]
    pub fn get_write_seqn(&self) -> u32 {
        self.write_seqn
    }

    /// Get current value of write sequence number
    #[inline]
    pub fn get_overwrite_seqn(&self) -> u32 {
        self.overwrite_seqn
    }

    /// Returns the sequence number looping modulus
    #[inline]
    pub fn get_seqn_mod(&self) -> u32 {
        self.seqn_mod
    }

    /// Adds given increment to given sequence number looping
    /// at the buffer's sequence number modulus
    #[inline]
    pub fn seqn_add(&self, seqn: u32, incr: u32) -> u32 {
        seqn_add(seqn, incr, self.seqn_mod)
    }
}

/// Iteratates through a RaceBuffer
#[derive(Copy, Clone)]
pub struct RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    /// Target RaceBuffer
    race_buffer: &'b RaceBuffer<'a, E>,
    /// Sequence number of next entry to read
    read_seqn: u32,
}

impl<'a, 'b, E> RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    /// Create a new iterator over the RaceBuffer at the given starting sequence number
    pub fn new(race_buffer: &'b RaceBuffer<'a, E>, start_seqn: u32) -> Self {
        Self {
            race_buffer,
            read_seqn: start_seqn,
        }
    }
}

impl<'a, 'b, E> Iterator for RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    type Item = PossiblyMissed<E>;
    fn next(&mut self) -> Option<PossiblyMissed<E>> {
        if self.read_seqn == self.race_buffer.get_write_seqn() {
            None
        } else {
            let read_entry = self.race_buffer.read(self.read_seqn);
            self.read_seqn = seqn_add(self.read_seqn, 1, self.race_buffer.get_seqn_mod());
            Some(read_entry)
        }
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
        let mut too_small_storage = [MaybeUninit::<OrderedEntry>::uninit(); MIN_STORAGE_CAP - 1];
        assert!(RaceBuffer::new(&mut too_small_storage[..], false).is_err());
        assert!(RaceBuffer::new(&mut too_small_storage[..], true).is_err());

        let input_sizes = [5, 6, 7, 8, 9, 12, 16];

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
        assert_eq!(&[4, 4, 4, 8, 8, 8, 16][..], &rounded_output_sizes[..]);
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
    fn test_read() {
        const STORAGE_CAP: usize = 8;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();

        for i in 0..16 {
            assert_eq!(buf.read(i), PossiblyMissed::Missed);
        }
        for i in 0..16 {
            buf.write(OrderedEntry::from_index(i));
        }
        for i in 0..8 {
            assert_eq!(buf.read(i), PossiblyMissed::Missed);
        }
        for i in 8..16 {
            assert_eq!(
                buf.read(i),
                PossiblyMissed::Entry(OrderedEntry::from_index(i as u32))
            );
        }
        for i in 16..32 {
            assert_eq!(buf.read(i), PossiblyMissed::Missed);
        }
    }

    #[test]
    fn test_iter() {
        const STORAGE_CAP: usize = 8;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
        {
            let mut iter = buf.iter(0);
            for _ in 0..32 {
                // Should not increment past write sequence num
                assert_eq!(iter.next(), None);
            }
        }
        for i in 0..16 {
            buf.write(OrderedEntry::from_index(i));
        }
        {
            let mut iter = buf.iter(4);
            for _ in 4..8 {
                assert_eq!(iter.next(), Some(PossiblyMissed::Missed));
            }
            for i in 8..16 {
                assert_eq!(
                    iter.next(),
                    Some(PossiblyMissed::Entry(OrderedEntry::from_index(i)))
                );
            }
            for _ in 16..32 {
                assert_eq!(iter.next(), None);
            }
        }
        {
            let mut iter = buf.iter(12);
            for i in 12..16 {
                assert_eq!(
                    iter.next(),
                    Some(PossiblyMissed::Entry(OrderedEntry::from_index(i)))
                );
            }
            for _ in 16..32 {
                assert_eq!(iter.next(), None);
            }
        }
    }

    #[test]
    fn test_get_linear_slices() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
        assert_eq!(buf.get_linear_slices(), (&[][..], &[][..]));
        for i in 0..2 {
            buf.write(OrderedEntry::from_index(i));
        }
        assert_eq!(
            buf.get_linear_slices(),
            (
                &[OrderedEntry::from_index(0), OrderedEntry::from_index(1)][..],
                &[][..]
            )
        );
        for i in 2..6 {
            buf.write(OrderedEntry::from_index(i));
        }
        assert_eq!(
            buf.get_linear_slices(),
            (
                &[OrderedEntry::from_index(2), OrderedEntry::from_index(3)][..],
                &[OrderedEntry::from_index(4), OrderedEntry::from_index(5)][..]
            )
        );
        for i in 6..8 {
            buf.write(OrderedEntry::from_index(i));
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
