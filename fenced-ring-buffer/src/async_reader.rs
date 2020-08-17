//! Reader of the FencedRingBuffer. Can asynchronously read from a writer::FencedRingBuffer into its own buffer.
//! To construct a reader::FencedReader, a Snapper must be implemented, which specifies how to access
//! the fields of the target FencedRingBuffer.
use crate::{get_seqn_index, num_missed, Entry, SeqNum, WholeEntry};
use std::cmp::min;

/// Used to "snap" observations of the FencedRingBuffer's write sequence number
/// or entries in the FencedRingBuffer's backing storage. Each Snapper access
/// should have sequential consistency with the memory access of the FencedRingBuffer writer
pub trait Snapper<E>
where
    E: Entry,
{
    /// Error during snapping
    type Error: std::error::Error;

    /// Take a snapshot of the high 32 bits of the write sequence number of the FencedRingBuffer
    fn snap_write_seqn_high(&self) -> Result<u32, Self::Error>;
    /// Take a snapshot of the low 32 bits of the write sequence number of the FencedRingBuffer
    fn snap_write_seqn_low(&self) -> Result<u32, Self::Error>;

    /// Take a snapshot of the high 32 bits of the overwrite sequence number of the FencedRingBuffer
    fn snap_overwrite_seqn_high(&self) -> Result<u32, Self::Error>;
    /// Take a snapshot of the low 32 bits of the overwrite sequence number of the FencedRingBuffer
    fn snap_overwrite_seqn_low(&self) -> Result<u32, Self::Error>;

    /// Take a snapshot of the FencedRingBuffer's backing storage at the given index
    fn snap_storage(&self, index: usize) -> Result<E, Self::Error>;
}

/// Used to read from a FencedRingBuffer asynchronously
pub struct FencedReader<E, S>
where
    E: Entry,
    S: Snapper<E>,
{
    /// Struct for reading writer state
    snapper: S,
    /// Sequence number of next entry to be read
    read_seqn: SeqNum,
    /// Capacity of backing storage
    storage_cap: usize,
    /// Vec used to store temporary snapshot of new entries in the buffer
    buf_snapshot: Vec<E>,
    /// Cached prefix, not put into buffer until suffix is successfully read
    stored_prefix: Option<E>,
}

impl<E, S> FencedReader<E, S>
where
    E: Copy + PartialEq + Entry,
    S: Snapper<E>,
{
    /// Create new FencedReader
    pub fn new(snapper: S, storage_cap: usize) -> FencedReader<E, S> {
        FencedReader {
            snapper,
            read_seqn: 0.into(),
            storage_cap,
            buf_snapshot: Vec::new(),
            stored_prefix: None,
        }
    }

    /// Attempt to read all new entries in buffer into given output vector
    /// Returns the number of entries missed before those that were read
    pub fn read(&mut self, out: &mut Vec<WholeEntry<E>>) -> Result<u64, S::Error> {
        // Store original read seqn for fallback upon error
        let reset_read_seqn = self.read_seqn;
        let pre_overwrite_seqn = self.snap_overwrite_seqn()?;
        let pre_write_seqn = self.snap_write_seqn()?;

        // If writer has overwritten unread entries between reads, store missed and correct read_seqn
        let mut n_missed_before_read = num_missed(self.read_seqn, pre_overwrite_seqn);
        self.read_seqn += n_missed_before_read;

        // Perform reads into snapshot buffer up to write sequence number
        self.buf_snapshot.clear();
        let first_read_seqn = self.read_seqn;
        while self.read_seqn != pre_write_seqn {
            let storage_index = get_seqn_index(self.storage_cap, self.read_seqn, false);
            let entry_read = self.snap_storage(storage_index).map_err(|e| {
                self.read_seqn = reset_read_seqn;
                e
            })?;
            self.buf_snapshot.push(entry_read);
            self.read_seqn += 1;
        }

        // Calculate number of entries in snapshot buffer that may have been overwritten
        let post_overwrite_seqn = self.snap_overwrite_seqn().map_err(|e| {
            self.read_seqn = reset_read_seqn;
            e
        })?;
        let n_overwritten_in_snap = min(
            num_missed(first_read_seqn, post_overwrite_seqn),
            (self.buf_snapshot.len() as u64).into(),
        );
        // If any entries were missed and there is a stored prefix, then the entry after the prefix was missed.
        // The prefix is dropped and added to the missed count
        if (u64::from(n_missed_before_read) > 0 || u64::from(n_overwritten_in_snap) > 0)
            && self.drop_prefix()
        {
            n_missed_before_read += 1;
        }

        // Store valid entries in read buffer
        for entry in &mut self.buf_snapshot[u64::from(n_overwritten_in_snap) as usize..] {
            Self::store(&mut self.stored_prefix, *entry, out);
        }
        Ok((n_missed_before_read + n_overwritten_in_snap).into())
    }

    /// Store given entry in given read buffer
    #[inline]
    fn store(stored_prefix: &mut Option<E>, entry: E, out: &mut Vec<WholeEntry<E>>) {
        if let Some(prefix) = stored_prefix.take() {
            out.push(WholeEntry::Double(prefix, entry));
        } else if entry.is_prefix() {
            *stored_prefix = Some(entry);
        } else {
            out.push(WholeEntry::Single(entry));
        }
    }

    /// Drop stored prefix, returning false if it was already None
    #[inline]
    fn drop_prefix(&mut self) -> bool {
        self.stored_prefix.take().is_some()
    }

    fn snap_storage(&self, index: usize) -> Result<E, S::Error> {
        self.snapper.snap_storage(index)
    }

    fn snap_write_seqn(&mut self) -> Result<SeqNum, S::Error> {
        Self::snap_seqn(
            || self.snapper.snap_write_seqn_high(),
            || self.snapper.snap_write_seqn_low(),
        )
    }

    fn snap_overwrite_seqn(&mut self) -> Result<SeqNum, S::Error> {
        Self::snap_seqn(
            || self.snapper.snap_overwrite_seqn_high(),
            || self.snapper.snap_overwrite_seqn_low(),
        )
    }

    /// Get a consistent snapshot of a sequence number, retrying if inconsistency is detected
    fn snap_seqn<F, G>(snap_high: F, snap_low: G) -> Result<SeqNum, S::Error>
    where
        F: Fn() -> Result<u32, S::Error>,
        G: Fn() -> Result<u32, S::Error>,
    {
        let mut initial_high;
        let mut final_high;
        let mut low;
        // Note: This will loop until a consistent snapshot is acquired. If the high word is incremented during
        // the snapshot, then the snapshot will not be consistent. However, the high word is only incremented every
        // 2^32 entries written to the buffer. We assume that the amount of time it takes to take a snapshot is
        // negligible compared to the time it takes to increment the high word. Therefore, there should only be one
        // retry at most, in the case where the first snapshot attempt and an increment to the high word happen to overlap.
        while {
            // Wait until the sequence number high word is not getting updated
            initial_high = Self::snap_consistent_high(&snap_high)?;
            low = snap_low()?;
            final_high = snap_high()?;
            // Check that the high word did not change between the two snapshots. If it did,
            // The low word is unusable because we are not sure which high word it corresponds to.
            // In that case, retry the whole sequence
            initial_high != final_high
        } {}
        Ok(SeqNum::new(final_high, low))
    }

    /// Get a snapshot of the high word of a sequence number, retrying if the "updating" bit is set
    fn snap_consistent_high<F>(snap_high: F) -> Result<u32, S::Error>
    where
        F: Fn() -> Result<u32, S::Error>,
    {
        let mut high;
        while {
            high = snap_high()?;
            SeqNum::has_updating_high_bit_set(high)
        } {}
        Ok(high)
    }
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use super::*;
    use crate::test_support::{OrderedEntry, PtrSnapper};
    use crate::FencedRingBuffer;
    use core::mem::MaybeUninit;

    #[test]
    fn test_async_read() {
        const STORAGE_CAP: usize = 4;
        let mut storage = [MaybeUninit::uninit(); STORAGE_CAP as usize];
        let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();
        let buf_ptr = &buf as *const FencedRingBuffer<'_, OrderedEntry>;
        let snapper = PtrSnapper::new(buf_ptr);
        let mut out = Vec::new();
        let mut buf_reader = FencedReader::new(snapper, STORAGE_CAP);

        assert_eq!(0, buf_reader.read(&mut out).unwrap());

        for i in 0..2 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(0, buf_reader.read(&mut out).unwrap());
        assert_eq!(
            vec![
                WholeEntry::Single(OrderedEntry::from_index(0)),
                WholeEntry::Single(OrderedEntry::from_index(1)),
            ],
            out
        );

        for i in 2..8 {
            buf.push(OrderedEntry::from_index(i));
        }
        // Missed 2, 3
        assert_eq!(2, buf_reader.read(&mut out).unwrap());
        assert_eq!(
            vec![
                WholeEntry::Single(OrderedEntry::from_index(0)),
                WholeEntry::Single(OrderedEntry::from_index(1)),
                WholeEntry::Single(OrderedEntry::from_index(4)),
                WholeEntry::Single(OrderedEntry::from_index(5)),
                WholeEntry::Single(OrderedEntry::from_index(6)),
                WholeEntry::Single(OrderedEntry::from_index(7)),
            ],
            out
        );

        out.clear();
        // Read in the middle of a double entry should wait until suffix is read to output whole double
        buf.push(OrderedEntry::from_index_prefix(8));
        assert_eq!(0, buf_reader.read(&mut out).unwrap());
        assert_eq!(Vec::<WholeEntry<OrderedEntry>>::new(), out);
        buf.push(OrderedEntry::from_index_suffix(9));
        assert_eq!(0, buf_reader.read(&mut out).unwrap());
        assert_eq!(
            vec![WholeEntry::Double(
                OrderedEntry::from_index_prefix(8),
                OrderedEntry::from_index_suffix(9)
            ),],
            out
        );

        out.clear();
        // If suffix is dropped, prefix should also be dropped
        buf.push(OrderedEntry::from_index_prefix(10));
        assert_eq!(0, buf_reader.read(&mut out).unwrap());
        assert_eq!(Vec::<WholeEntry<OrderedEntry>>::new(), out);
        buf.push(OrderedEntry::from_index_suffix(11));
        for i in 12..16 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(2, buf_reader.read(&mut out).unwrap());
        assert_eq!(
            vec![
                WholeEntry::Single(OrderedEntry::from_index(12)),
                WholeEntry::Single(OrderedEntry::from_index(13)),
                WholeEntry::Single(OrderedEntry::from_index(14)),
                WholeEntry::Single(OrderedEntry::from_index(15)),
            ],
            out
        );

        out.clear();
        // Overwriting a double entry should occur atomically, even if only the
        // prefix's cell has been used for a new entry
        buf.push_double(
            OrderedEntry::from_index_prefix(16),
            OrderedEntry::from_index_suffix(17),
        );
        for i in 18..21 {
            buf.push(OrderedEntry::from_index(i));
        }
        assert_eq!(2, buf_reader.read(&mut out).unwrap());
        assert_eq!(
            vec![
                WholeEntry::Single(OrderedEntry::from_index(18)),
                WholeEntry::Single(OrderedEntry::from_index(19)),
                WholeEntry::Single(OrderedEntry::from_index(20)),
            ],
            out
        );
    }
}
