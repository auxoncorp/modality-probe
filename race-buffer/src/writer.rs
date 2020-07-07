use crate::{get_cursor_index, Entry};
use core::iter::Iterator;
use core::mem::size_of;
use core::mem::MaybeUninit;

pub enum ReadEntry<E>
where
    E: Entry,
{
    NotYetWritten,
    Missed,
    Entry(E),
}

#[inline]
/// Round given length down to a power of 2
fn round_to_power_2(length: usize) -> usize {
    let exp: usize = size_of::<usize>() * 8 - (length.leading_zeros() as usize) - 1;
    1 << exp
}

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
    pub fn new(storage: &'a mut [MaybeUninit<E>], use_base_2_indexing: bool) -> RaceBuffer<'a, E> {
        let truncated_len = if use_base_2_indexing {
            round_to_power_2(storage.len())
        } else {
            storage.len()
        };
        RaceBuffer {
            wcurs: 0,
            owcurs: 0,
            storage: &mut storage[..truncated_len],
            use_base_2_indexing,
        }
    }

    /// Write single entry to buffer
    pub fn write(&mut self, entry: E) {
        if self.wcurs == self.owcurs {
            // If overwriting double, increment overwrite cursor by 2
            if self.wcurs >= self.storage.len()
                && unsafe { self.read_storage(self.wcurs).is_prefix() }
            {
                self.owcurs += 2;
            } else {
                self.owcurs += 1;
            }
        }
        self.write_to_storage(self.wcurs, entry);
        self.wcurs += 1;
    }

    #[inline]
    /// Get value of backing storage corresponding to given index
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

    pub fn iter<'b>(&'b self, start_rcurs: usize) -> RaceBufferIter<'a, 'b, E> {
        RaceBufferIter::new(self, start_rcurs)
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    #[inline]
    /// Get current value of write cursor
    pub(crate) fn read_wcurs(&self) -> usize {
        self.wcurs
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    #[inline]
    /// Get current value of write cursor
    pub(crate) fn read_owcurs(&self) -> usize {
        self.owcurs
    }

    #[cfg(feature = "std")]
    #[cfg(test)]
    #[inline]
    pub(crate) fn get_slice(&self) -> &[MaybeUninit<E>] {
        self.storage
    }
}

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
            ReadEntry::NotYetWritten => None,
            ReadEntry::Missed => Some(None),
            ReadEntry::Entry(e) => {
                self.rcurs += 1;
                Some(Some(e))
            }
        }
    }
}
