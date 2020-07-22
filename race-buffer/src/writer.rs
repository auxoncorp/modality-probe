use crate::{get_cursor_index, Entry};
use core::iter::Iterator;
use core::mem::size_of;
use core::mem::MaybeUninit;

#[cfg(not(feature = "std"))]
use core::fmt;
#[cfg(feature = "std")]
use std::fmt;

/// Minimum allowed capacity of backing storage
pub const MIN_STORAGE_CAP: usize = 4;
pub struct SizeError;

impl fmt::Debug for SizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "Storage capacity must be at least {}",
            MIN_STORAGE_CAP
        ))
    }
}

#[inline]
/// Round given length down to a power of 2
fn round_to_power_2(length: usize) -> usize {
    let exp: usize = size_of::<usize>() * 8 - (length.leading_zeros() as usize) - 1;
    1 << exp
}

/// A single entry that has been read, which may or may not be currently available
pub enum ReadEntry<E>
where
    E: Entry,
{
    NotYetWritten,
    Missed,
    Entry(E),
}

/// An entry or double entry that has just been overwritten
pub enum OverwrittenEntry<E>
where
    E: Entry,
{
    None,
    Single(E),
    Double(E, E),
}

#[derive(Debug)]
#[repr(C)]
/// Struct used to write to buffer
pub struct RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Write cursor: Cursor pointing to where the next entry will be written
    wcurs: usize,
    /// Overwrite cursor: Entries in front of wcurs but behind owcurs are in the process of being overwritten
    owcurs: usize,
    /// Backing storage
    storage: &'a mut [MaybeUninit<E>],
    /// Indicates if backing storage should be truncated to a power of 2 length
    /// in order to use optimized indexing
    use_base_2_indexing: bool,
}

impl<'a, E> RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Create new RaceBuffer. Returns error if storage size is not power of 2
    pub fn new(storage: &'a mut [MaybeUninit<E>]) -> Result<RaceBuffer<'a, E>, SizeError> {
        let use_base_2_indexing = storage.len().is_power_of_two();
        if storage.len() < MIN_STORAGE_CAP {
            Err(SizeError)
        } else {
            Ok(RaceBuffer {
                wcurs: 0,
                owcurs: storage.len(),
                storage,
                use_base_2_indexing,
            })
        }
    }

    /// Create new RaceBuffer with properly aligned backing storage
    #[inline]
    pub fn new_from_bytes(bytes: &'a mut [u8]) -> Result<RaceBuffer<'a, E>, SizeError> {
        let (_prefix, buf, _suffix) = Self::align_from_bytes(bytes);
        buf
    }

    /// Create new RaceBuffer with properly aligned backing storage, return unused bytes
    #[inline]
    pub fn align_from_bytes(
        bytes: &'a mut [u8],
    ) -> (
        &'a mut [u8],
        Result<RaceBuffer<'a, E>, SizeError>,
        &'a mut [u8],
    ) {
        // Safe because storage is treated as uninit after transmutation
        let (prefix, storage, suffix) = unsafe { bytes.align_to_mut() };
        (prefix, RaceBuffer::new(storage), suffix)
    }

    /// Write single entry to buffer
    pub fn write(&mut self, entry: E) -> OverwrittenEntry<E> {
        let mut overwritten = OverwrittenEntry::None;
        if self.wcurs == self.owcurs {
            // Reading storage is safe after checking if buffer has looped at least once
            if self.wcurs >= self.storage.len()
                && unsafe { self.read_storage(self.wcurs).is_prefix() }
            {
                // If overwriting double, increment overwrite cursor by 2
                overwritten = unsafe {
                    OverwrittenEntry::Double(
                        self.read_storage(self.owcurs),
                        self.read_storage(self.owcurs + 1),
                    )
                };
                self.owcurs += 2;
            } else {
                overwritten = unsafe { OverwrittenEntry::Single(self.read_storage(self.owcurs)) };
                self.owcurs += 1;
            }
        }
        self.write_to_storage(self.wcurs, entry);
        self.wcurs += 1;
        overwritten
    }

    /// Get value of backing storage corresponding to given index
    #[inline]
    pub(crate) unsafe fn read_storage(&self, curs: usize) -> E {
        self.storage[get_cursor_index(self.storage.len(), curs, self.use_base_2_indexing)]
            .assume_init()
    }

    #[inline]
    fn write_to_storage(&mut self, curs: usize, entry: E) {
        self.storage[get_cursor_index(self.storage.len(), curs, self.use_base_2_indexing)] =
            MaybeUninit::new(entry);
    }

    #[inline]
    pub fn read(&self, curs: usize) -> ReadEntry<E> {
        if self.wcurs <= curs {
            ReadEntry::NotYetWritten
        } else if self.owcurs > curs + self.storage.len() {
            ReadEntry::Missed
        } else {
            ReadEntry::Entry(unsafe {
                self.read_storage(get_cursor_index(
                    self.storage.len(),
                    curs,
                    self.use_base_2_indexing,
                ))
            })
        }
    }

    #[inline]
    pub fn iter<'b>(&'b self, start_rcurs: usize) -> RaceBufferIter<'a, 'b, E> {
        RaceBufferIter::new(self, start_rcurs)
    }

    #[inline]
    pub fn as_slice(&self) -> &[MaybeUninit<E>] {
        self.storage
    }

    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    #[cfg(test)]
    #[inline]
    /// Get current value of write cursor
    pub(crate) fn get_wcurs(&self) -> usize {
        self.wcurs
    }

    #[cfg(test)]
    #[inline]
    /// Get current value of write cursor
    pub(crate) fn get_owcurs(&self) -> usize {
        self.owcurs
    }
}

#[derive(Copy, Clone)]
pub struct RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    race_buffer: &'b RaceBuffer<'a, E>,
    rcurs: usize,
}

impl<'a, 'b, E> RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    /// Create a new iterator over the RaceBuffer at the given starting cursor
    pub fn new(race_buffer: &'b RaceBuffer<'a, E>, start_curs: usize) -> Self {
        Self {
            race_buffer,
            rcurs: start_curs,
        }
    }
}

impl<'a, 'b, E> Iterator for RaceBufferIter<'a, 'b, E>
where
    E: Entry,
{
    type Item = Option<E>;

    fn next(&mut self) -> Option<Option<E>> {
        match self.race_buffer.read(self.rcurs) {
            // Indicate that the iterator is finished
            ReadEntry::NotYetWritten => None,
            // Iterator not finished, but value was missed
            ReadEntry::Missed => Some(None),
            ReadEntry::Entry(e) => {
                self.rcurs += 1;
                Some(Some(e))
            }
        }
    }
}
