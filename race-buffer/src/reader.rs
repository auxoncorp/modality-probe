//! Reader of the RaceBuffer. Can asynchronously read from a writer::RaceBuffer into its own buffer.
//! To construct a reader::RaceBufferReader, a Snapper must be implemented, which specifies how to access
//! the fields of the target RaceBuffer.
use crate::{get_seqn_index, get_seqn_mod, num_missed, seqn_add, Entry, PossiblyMissed};
use std::cmp::min;
use std::error::Error;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
/// Used to "snap" observations of the RaceBuffer's write sequence number
/// or entries in the RaceBuffer's backing storage. Each Snapper access
/// should have sequential consistency with the memory access of the RaceBuffer writer
pub trait Snapper<E>
where
    E: Entry,
{
    /// Take a snapshot of the write sequence number of the RaceBuffer
    fn snap_write_seqn(&self) -> Result<u32>;
    /// Take a snapshot of the overwrite sequence number of the RaceBuffer
    fn snap_overwrite_seqn(&self) -> Result<u32>;
    /// Take a snapshot of the RaceBuffer's backing storage at the given index
    fn snap_storage(&self, index: u32) -> Result<E>;
}

/// Struct used to read from a RaceBuffer asynchronously
pub struct RaceBufferReader<E, S>
where
    E: Entry,
    S: Snapper<E>,
{
    /// Struct for reading writer state
    snapper: S,
    /// Sequence number of next entry to be read
    read_seqn: u32,
    /// Capacity of backing storage
    storage_cap: u32,
    /// Cached prefix, not put into buffer until suffix is successfully read
    stored_prefix: Option<E>,
    /// Sequence number modulus for wrapping to zero
    seqn_mod: u32,
}

impl<E, S> RaceBufferReader<E, S>
where
    E: Copy + PartialEq + Entry,
    S: Snapper<E>,
{
    /// Create new RaceBufferReader
    pub fn new(snapper: S, storage_cap: u32) -> RaceBufferReader<E, S> {
        RaceBufferReader {
            snapper,
            read_seqn: 0,
            storage_cap,
            stored_prefix: None,
            seqn_mod: get_seqn_mod(storage_cap),
        }
    }

    /// Attempt to read all new entries in race buffer into given read buffer
    /// Returns the number of entries read (both missed and present)
    pub fn read(&mut self, rbuf: &mut Vec<PossiblyMissed<E>>) -> Result<u32> {
        let pre_overwrite_seqn = self.snapper.snap_overwrite_seqn()?;
        let pre_write_seqn = self.snapper.snap_write_seqn()?;

        // If writer has overwritten unread entries between reads, store missed and correct read_seqn
        let n_missed_before_read = num_missed(
            self.read_seqn,
            pre_overwrite_seqn,
            pre_write_seqn,
            self.seqn_mod,
        );
        self.store_missed_items(n_missed_before_read, rbuf);
        self.read_seqn = seqn_add(self.read_seqn, n_missed_before_read, self.seqn_mod);

        // Perform reads into snapshot buffer up to write sequence number
        let first_read_seqn = self.read_seqn;
        let mut buf_snapshot: Vec<E> = Vec::new();
        while self.read_seqn != pre_write_seqn {
            let storage_index = get_seqn_index(self.storage_cap, self.read_seqn, false);
            // Storage index never greater than u32::MAX
            buf_snapshot.push(self.snapper.snap_storage(storage_index as u32)?);
            self.read_seqn = seqn_add(self.read_seqn, 1, self.seqn_mod);
        }

        // Calculate number of entries in snapshot buffer that may have been overwritten
        let post_overwrite_seqn = self.snapper.snap_overwrite_seqn()?;
        let post_write_seqn = self.snapper.snap_write_seqn()?;

        // Cast to u32 safe because buffer is no bigger than u32::MAX
        let n_overwritten_in_snap = min(
            num_missed(
                first_read_seqn,
                post_overwrite_seqn,
                post_write_seqn,
                self.seqn_mod,
            ),
            buf_snapshot.len() as u32,
        );
        self.store_missed_items(n_overwritten_in_snap, rbuf);

        // Store valid entries in read buffer
        for entry in &mut buf_snapshot[n_overwritten_in_snap as usize..] {
            self.store(*entry, rbuf);
        }
        Ok(self.read_seqn)
    }

    /// Store given entry in given read buffer
    #[inline]
    fn store(&mut self, entry: E, rbuf: &mut Vec<PossiblyMissed<E>>) {
        match self.stored_prefix {
            None => {
                if entry.is_prefix() {
                    self.stored_prefix = Some(entry);
                } else {
                    rbuf.push(PossiblyMissed::Entry(entry));
                }
            }
            Some(prefix) => {
                rbuf.push(PossiblyMissed::Entry(prefix));
                rbuf.push(PossiblyMissed::Entry(entry));
                self.stored_prefix = None;
            }
        }
    }

    /// Store single missed entries in read buffer, dropping stored prefix if present
    #[inline]
    fn store_missed_item(&mut self, rbuf: &mut Vec<PossiblyMissed<E>>) {
        match self.stored_prefix {
            None => {
                rbuf.push(PossiblyMissed::Missed);
            }
            Some(_) => {
                // Suffix missed, indicate 2 missed entries
                rbuf.push(PossiblyMissed::Missed);
                rbuf.push(PossiblyMissed::Missed);
                self.stored_prefix = None;
            }
        }
    }

    /// Store given number of missed entries in read buffer
    #[inline]
    fn store_missed_items(&mut self, num: u32, rbuf: &mut Vec<PossiblyMissed<E>>) {
        for _ in 0..num {
            self.store_missed_item(rbuf);
        }
    }

    /// Returns read sequence number
    #[inline]
    pub fn get_read_seqn(&self) -> u32 {
        self.read_seqn
    }

    /// Returns the sequence number looping modulus
    #[inline]
    pub fn get_seqn_mod(&self) -> u32 {
        self.seqn_mod
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::*;
    use crate::util::{OrderedEntry, RawPtrSnapper};
    use crate::writer;
    use core::mem::MaybeUninit;

    #[test]
    fn read_seqn() {
        const STORAGE_CAP: u32 = 8;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP as usize];
        let mut buf = writer::RaceBuffer::new(&mut storage[..], false).unwrap();
        let buf_ptr = &buf as *const writer::RaceBuffer<'_, OrderedEntry>;
        let snapper = RawPtrSnapper::new(buf_ptr);
        let mut rbuf = Vec::new();
        let mut buf_reader = RaceBufferReader::new(snapper, STORAGE_CAP);

        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());

        for i in 0..4 {
            buf.write(OrderedEntry::from_index(i));
        }
        assert_eq!(4, buf_reader.read(&mut rbuf).unwrap());

        for i in 4..16 {
            buf.write(OrderedEntry::from_index(i));
        }
        assert_eq!(16, buf_reader.read(&mut rbuf).unwrap());
    }
}
