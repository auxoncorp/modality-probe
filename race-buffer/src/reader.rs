use crate::{get_cursor_index, Entry};
use core::marker::PhantomData;
use std::cmp::min;
use std::error::Error;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
/// Used to "snap" observations of the RaceBuffer's write cursor
/// or entries in the RaceBuffer's backing storage. Each Snapper access
/// should have sequential consistency with the memory access of the RaceBuffer writer
pub trait Snapper<E>
where
    E: Entry,
{
    /// Take a snapshot of the write cursor of the RaceBuffer
    fn snap_wcurs(&self) -> Result<usize>;
    /// Take a snapshot of the overwrite cursor of the RaceBuffer
    fn snap_owcurs(&self) -> Result<usize>;
    /// Take a snapshot of the RaceBuffer's backing storage at the given index
    fn snap_storage(&self, index: usize) -> Result<E>;
}

/// Struct used to read from a RaceBuffer asynchronously
pub struct RaceBufferReader<E, S>
where
    E: Entry,
    S: Snapper<E>,
{
    /// Struct for reading writer state
    snapper: S,
    /// Reader's cursor
    rcurs: usize,
    /// Capacity of backing storage
    storage_cap: usize,
    /// Cached prefix, not put into buffer until suffix is successfully read
    stored_prefix: Option<E>,
    phantom: PhantomData<E>,
}

impl<E, S> RaceBufferReader<E, S>
where
    E: Copy + PartialEq + Entry,
    S: Snapper<E>,
{
    /// Create new RaceBufferReader
    pub fn new(snapper: S, storage_cap: usize) -> RaceBufferReader<E, S> {
        RaceBufferReader {
            snapper,
            rcurs: 0,
            storage_cap,
            stored_prefix: None,
            phantom: PhantomData,
        }
    }

    /// Attempt to read all new entries in race buffer into given read buffer
    pub fn read(&mut self, rbuf: &mut Vec<Option<E>>) -> Result<()> {
        let pre_wcurs = self.snapper.snap_wcurs()?;
        let pre_owcurs = self.snapper.snap_owcurs()?;

        if pre_owcurs > self.rcurs + self.storage_cap {
            // If writer has overwritten unread entries between reads, store nils and correct rcurs
            let num_missed = pre_owcurs - (self.rcurs + self.storage_cap);
            self.store_missed_items(num_missed, rbuf);
            self.rcurs = pre_owcurs - self.storage_cap;
        }

        // Perform reads into snapshot buffer up to write cursor
        let first_read = self.rcurs;
        let mut buf_snapshot: Vec<E> = Vec::new();
        while self.rcurs < pre_wcurs {
            let storage_index = get_cursor_index(self.storage_cap, self.rcurs, false);
            buf_snapshot.push(self.snapper.snap_storage(storage_index)?);
            self.rcurs += 1;
        }

        // Calculate number of entries in snapshot buffer that may have been overwritten
        let post_owcurs = self.snapper.snap_owcurs()?;
        let overlap = min(
            if post_owcurs > self.storage_cap + first_read {
                post_owcurs - (first_read + self.storage_cap)
            } else {
                0
            },
            buf_snapshot.len(),
        );

        if overlap != 0 {
            self.store_missed_items(overlap, rbuf);
        }

        // Store valid entries in read buffer
        for entry in &mut buf_snapshot[overlap..] {
            self.store(*entry, rbuf);
        }
        Ok(())
    }

    /// Store given entry in given read buffer
    #[inline]
    fn store(&mut self, entry: E, rbuf: &mut Vec<Option<E>>) {
        match self.stored_prefix {
            None => {
                if entry.is_prefix() {
                    self.stored_prefix = Some(entry);
                } else {
                    rbuf.push(Some(entry));
                }
            }
            Some(prefix) => {
                rbuf.push(Some(prefix));
                rbuf.push(Some(entry));
                self.stored_prefix = None;
            }
        }
    }

    #[inline]
    fn store_missed_item(&mut self, rbuf: &mut Vec<Option<E>>) {
        match self.stored_prefix {
            None => {
                rbuf.push(None);
            }
            Some(_) => {
                // Suffix missed, indicate 2 missed entries
                rbuf.push(None);
                rbuf.push(None);
                self.stored_prefix = None;
            }
        }
    }

    #[inline]
    /// Store given number of nil entries in given read buffer
    fn store_missed_items(&mut self, num: usize, rbuf: &mut Vec<Option<E>>) {
        for _ in 0..num {
            self.store_missed_item(rbuf);
        }
    }
}
