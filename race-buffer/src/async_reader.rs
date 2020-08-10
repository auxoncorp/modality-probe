//! Reader of the RaceBuffer. Can asynchronously read from a writer::RaceBuffer into its own buffer.
//! To construct a reader::RaceReader, a Snapper must be implemented, which specifies how to access
//! the fields of the target RaceBuffer.
use crate::{get_seqn_index, num_missed, Entry};
use std::cmp::min;

/// Used to "snap" observations of the RaceBuffer's write sequence number
/// or entries in the RaceBuffer's backing storage. Each Snapper access
/// should have sequential consistency with the memory access of the RaceBuffer writer
pub trait Snapper<E>
where
    E: Entry,
{
    /// Error during snapping
    type Error: std::error::Error;

    /// Take a snapshot of the write sequence number of the RaceBuffer
    fn snap_write_seqn(&self) -> Result<u64, Self::Error>;
    /// Take a snapshot of the overwrite sequence number of the RaceBuffer
    fn snap_overwrite_seqn(&self) -> Result<u64, Self::Error>;
    /// Take a snapshot of the RaceBuffer's backing storage at the given index
    fn snap_storage(&self, index: usize) -> Result<E, Self::Error>;
}

/// Used to read from a RaceBuffer asynchronously
pub struct RaceReader<E, S>
where
    E: Entry,
    S: Snapper<E>,
{
    /// Struct for reading writer state
    snapper: S,
    /// Sequence number of next entry to be read
    read_seqn: u64,
    /// Capacity of backing storage
    storage_cap: usize,
    /// Cached prefix, not put into buffer until suffix is successfully read
    stored_prefix: Option<E>,
}

impl<E, S> RaceReader<E, S>
where
    E: Copy + PartialEq + Entry,
    S: Snapper<E>,
{
    /// Create new RaceReader
    pub fn new(snapper: S, storage_cap: usize) -> RaceReader<E, S> {
        RaceReader {
            snapper,
            read_seqn: 0,
            storage_cap,
            stored_prefix: None,
        }
    }

    /// Attempt to read all new entries in race buffer into given read buffer
    /// Returns the number of entries missed before those that were read
    pub fn read(&mut self, rbuf: &mut Vec<E>) -> Result<u64, S::Error> {
        let pre_overwrite_seqn = self.snapper.snap_overwrite_seqn()?;
        let pre_write_seqn = self.snapper.snap_write_seqn()?;

        // If writer has overwritten unread entries between reads, store missed and correct read_seqn
        let mut n_missed_before_read = num_missed(self.read_seqn, pre_overwrite_seqn);
        self.read_seqn += n_missed_before_read;
        // If any entries were missed and there is a stored prefix, then the entry after the prefix was missed.
        // The prefix is dropped and added to the missed count.
        // Note: the read sequence number is updated above because the prefix was included in the last read
        if n_missed_before_read > 0 && self.drop_prefix() {
            n_missed_before_read += 1;
        }

        // Perform reads into snapshot buffer up to write sequence number
        let first_read_seqn = self.read_seqn;
        let mut buf_snapshot: Vec<E> = Vec::new();
        while self.read_seqn != pre_write_seqn {
            let storage_index = get_seqn_index(self.storage_cap, self.read_seqn, false);
            buf_snapshot.push(self.snapper.snap_storage(storage_index)?);
            self.read_seqn += 1;
        }

        // Calculate number of entries in snapshot buffer that may have been overwritten
        let post_overwrite_seqn = self.snapper.snap_overwrite_seqn()?;
        let n_overwritten_in_snap = min(
            num_missed(first_read_seqn, post_overwrite_seqn),
            buf_snapshot.len() as u64,
        );
        // If any entries were missed and there is a stored prefix, then the entry after the prefix was missed.
        // The prefix is dropped and added to the missed count (not overwritten during snap)
        if n_overwritten_in_snap > 0 && self.drop_prefix() {
            n_missed_before_read += 1;
        }

        // Store valid entries in read buffer
        for entry in &mut buf_snapshot[n_overwritten_in_snap as usize..] {
            self.store(*entry, rbuf);
        }
        Ok(n_missed_before_read + n_overwritten_in_snap)
    }

    /// Store given entry in given read buffer
    #[inline]
    fn store(&mut self, entry: E, rbuf: &mut Vec<E>) {
        if let Some(prefix) = self.stored_prefix.take() {
            rbuf.push(prefix);
            rbuf.push(entry);
        } else if entry.is_prefix() {
            self.stored_prefix = Some(entry);
        } else {
            rbuf.push(entry);
        }
    }

    /// Drop stored prefix, returning false if it was already None
    #[inline]
    fn drop_prefix(&mut self) -> bool {
        self.stored_prefix.take().is_some()
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::*;
    use crate::util::{OrderedEntry, RawPtrSnapper};
    use crate::RaceBuffer;
    use core::mem::MaybeUninit;

    #[test]
    fn test_reads() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP as usize];
        let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
        let buf_ptr = &buf as *const RaceBuffer<'_, OrderedEntry>;
        let snapper = RawPtrSnapper::new(buf_ptr);
        let mut rbuf = Vec::new();
        let mut buf_reader = RaceReader::new(snapper, STORAGE_CAP);

        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());

        for i in 0..2 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(
            vec![OrderedEntry::from_index(0), OrderedEntry::from_index(1),],
            rbuf
        );

        for i in 2..8 {
            buf.push(OrderedEntry::from_index(i));
        }
        // Missed 2, 3
        assert_eq!(2, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(
            vec![
                OrderedEntry::from_index(0),
                OrderedEntry::from_index(1),
                OrderedEntry::from_index(4),
                OrderedEntry::from_index(5),
                OrderedEntry::from_index(6),
                OrderedEntry::from_index(7),
            ],
            rbuf
        );

        rbuf.clear();
        // Read in the middle of a double entry should wait until suffix is read to output whole double
        buf.push(OrderedEntry::from_index_prefix(8));
        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(Vec::<OrderedEntry>::new(), rbuf);
        buf.push(OrderedEntry::from_index_suffix(9));
        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(
            vec![
                OrderedEntry::from_index_prefix(8),
                OrderedEntry::from_index_suffix(9),
            ],
            rbuf
        );

        rbuf.clear();
        // If suffix is dropped, prefix should also be dropped
        buf.push(OrderedEntry::from_index_prefix(10));
        assert_eq!(0, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(Vec::<OrderedEntry>::new(), rbuf);
        buf.push(OrderedEntry::from_index_suffix(11));
        for i in 12..16 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(2, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(
            vec![
                OrderedEntry::from_index(12),
                OrderedEntry::from_index(13),
                OrderedEntry::from_index(14),
                OrderedEntry::from_index(15),
            ],
            rbuf
        );

        rbuf.clear();
        // Overwriting a double entry should occur atomically, even if only the
        // prefix's cell has been used for a new entry
        buf.push_double(
            OrderedEntry::from_index_prefix(16),
            OrderedEntry::from_index_suffix(17),
        );
        for i in 18..21 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(2, buf_reader.read(&mut rbuf).unwrap());
        assert_eq!(
            vec![
                OrderedEntry::from_index(18),
                OrderedEntry::from_index(19),
                OrderedEntry::from_index(20),
            ],
            rbuf
        );
    }
}
