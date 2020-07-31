//! RaceBuffer, a single producer, single consumer, shared memory ring buffer which maintains
//! consistency while operating under race conditions.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]

use core::cmp::PartialEq;
use core::marker::Copy;

/// The maximum sequence number modulus. This generally should be u32 MAX, but can be lowered
/// for testing.
const SEQN_MOD_MAX: u32 = u32::MAX;

/// Return the sequence number modulus that should be used for a buffer of given capacity
/// A sequence number modulus is the number at which sequence numbers wrap around to zero.
/// They are unique to each buffer capacity, and are calculated by rounding down from SEQN_MOD_MAX
/// to the nearest multiple of the buffer capacity. It is assumed that the writer never eclipses
/// the reader by an entire sequence number modulus.
///
/// Note: sequence numbers are calculated this way to ensure that when the sequence numbers wrap,
/// they will go from the last cell of the storage to the 0th.
fn get_seqn_mod(cap: u32) -> u32 {
    SEQN_MOD_MAX - (SEQN_MOD_MAX % cap)
}

/// Increments given sequence number by given amount, looping at SEQN_MOD
#[inline]
fn seqn_add(seqn: u32, incr: u32, seqn_mod: u32) -> u32 {
    if seqn_mod - seqn > incr {
        seqn + incr
    } else {
        incr - (seqn_mod - seqn)
    }
}

/// Returns the corresponding index in backing storage to given sequence number
#[inline]
fn get_seqn_index(storage_cap: u32, seqn: u32, use_base_2_indexing: bool) -> usize {
    // Cast to usize safe because index cannot be greater than usize
    if use_base_2_indexing {
        // Index is lowest n bits of seqn where storage_cap is 2^n
        (seqn & (storage_cap - 1)) as usize
    } else {
        (seqn % storage_cap) as usize
    }
}

/// Calculate the number of entries missed based on the read, overwrite, and write sequence numbers
#[inline]
fn num_missed(read_seqn: u32, overwrite_seqn: u32, write_seqn: u32, seqn_mod: u32) -> u32 {
    if overwrite_seqn <= write_seqn && write_seqn < read_seqn {
        // Read seqn must loop to catch up
        overwrite_seqn + (seqn_mod - read_seqn)
    } else if read_seqn < overwrite_seqn && (overwrite_seqn < write_seqn || write_seqn < read_seqn)
    {
        // Read seqn must catch up without looping
        overwrite_seqn - read_seqn
    } else {
        // Read seqn is caught up
        0
    }
}


/// A single entry which may have been missed
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum PossiblyMissed<E>
where
    E: Entry,
{
    /// An entry that is no longer present in the buffer, or was never written
    Missed,
    /// An entry currently present in the buffer
    Entry(E),
}

impl<E> PossiblyMissed<E>
where
    E: Entry,
{
    /// Unwraps the entry, panicking if it was missed
    pub fn assume_not_missed(self) -> E {
        match self {
            Self::Missed => panic!("Entry assumed to be present but actually was missed"),
            Self::Entry(e) => e,
        }
    }
}

/// Entry that can be stored in a RaceBuffer
pub trait Entry: Copy + PartialEq {
    /// Return true if entry is the first in a double entry
    fn is_prefix(&self) -> bool;
}

#[cfg(feature = "std")]
pub mod reader;
pub mod writer;

#[cfg(feature = "std")]
#[cfg(test)]
mod util;

#[cfg(feature = "std")]
#[cfg(test)]
pub mod tests {
    use super::*;

    use core::mem::MaybeUninit;
    use crossbeam;
    use rand::Rng;
    use std::sync::atomic::AtomicU32;
    use std::sync::atomic::Ordering;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;
    use util::*;

    #[test]
    fn test_num_missed() {
        const TEST_SEQN_MOD: u32 = 16;

        // In the following three orders, the read sequence number is between (inclusive) the overwrite and write sequence
        // numbers (in terms of the modulus space),
        // where entries are currently present in the buffer, so no entries were missed.

        // Order: OW, R, W
        assert_eq!(num_missed(0, 0, 4, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(5, 3, 7, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(8, 4, 8, TEST_SEQN_MOD), 0);

        // Order: W, OW, R
        // In these cases, the write sequence number has wrapped around the sequence number modulus one additional time
        // compared to the other two sequence numbers
        assert_eq!(num_missed(15, 14, 2, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(12, 12, 0, TEST_SEQN_MOD), 0);

        // Order: W, OW, R
        // In these cases, the write and read sequence numbers have wrapped around the sequence number modulus
        // one additional time compared to the overwrite sequence number
        assert_eq!(num_missed(1, 15, 3, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(1, 13, 1, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(0, 12, 0, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(0, 13, 1, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(1, 13, 1, TEST_SEQN_MOD), 0);

        // In the following two orders, the read sequence number is behind (exclusive) the overwrite sequence
        // number (in terms of the modulus space), so the reader missed the difference between the read and overwrite
        // sequence numbers

        // Order: R, OW, W
        assert_eq!(num_missed(0, 1, 5, TEST_SEQN_MOD), 1);
        assert_eq!(num_missed(1, 10, 14, TEST_SEQN_MOD), 9);

        // Order: W, R, OW
        // In these cases, the write sequence number has wrapped around the sequence number modulus one additional time
        // compared to the other two sequence numbers
        assert_eq!(num_missed(13, 15, 3, TEST_SEQN_MOD), 2);
        assert_eq!(num_missed(2, 13, 1, TEST_SEQN_MOD), 11);

        // In the following order, the write and overwrite sequence numbers have wrapped one more time than the read
        // sequence number. To catch up, the reader must wrap around and reach the overwrite sequence number.
        // Therefore, the reader has missed entries with sequence numbers between the read cursor (inclusive) and
        // the sequence number modulus (exclusive), as well as entries with sequence numbers between 0 (inclusive)
        // and the overwrite cursor (exclusive).
        // Order: OW, W, R
        assert_eq!(num_missed(15, 0, 4, TEST_SEQN_MOD), 1);
        assert_eq!(num_missed(6, 1, 5, TEST_SEQN_MOD), 11);

        // Before any items are written, the write and overwrite sequence numbers are equal to 0. In this case, if the
        // read sequence number is at 0, then no items have been missed. Checking any other read sequence number should
        // return a value greater than 0, as there are no entries available to read at those points.
        assert_eq!(num_missed(0, 0, 0, TEST_SEQN_MOD), 0);
        assert_eq!(num_missed(1, 0, 0, TEST_SEQN_MOD), 15);
        assert_eq!(num_missed(15, 0, 3, TEST_SEQN_MOD), 1);
    }

    // Perform many reads and writes concurrently,
    // check if read buffer is in order and consistent
    #[test]
    fn random_writes() {
        const NUM_WRITES: u32 = 160;
        const STORAGE_CAP: usize = 8;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        let num_read_r = Arc::new(AtomicU32::new(0));
        let num_read_w = num_read_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];

                let mut buf = writer::RaceBuffer::new(&mut storage[..], false).unwrap();
                assert!(buf.capacity() == STORAGE_CAP as u32);
                let buf_ptr = &buf as *const writer::RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();

                for i in 0..NUM_WRITES {
                    while i - num_read_w.load(Ordering::SeqCst) >= buf.get_seqn_mod() - 1 {}
                    buf.write(OrderedEntry::from_index(i));
                    std::thread::sleep(Duration::from_millis(10));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const writer::RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper::new(buf_ptr);
                let mut rbuf = Vec::new();
                let mut buf_reader = reader::RaceBufferReader::new(snapper, STORAGE_CAP as u32);
                while rbuf.len() < NUM_WRITES as usize {
                    buf_reader.read(&mut rbuf).unwrap();
                    num_read_r.store(rbuf.len() as u32, Ordering::SeqCst);
                    thread::sleep(Duration::from_millis(10));
                }
                thread::sleep(Duration::from_millis(100));
                buf_reader.read(&mut rbuf).unwrap();
                assert_eq!(rbuf.len(), NUM_WRITES as usize);
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }

    // Perform many reads and writes concurrently with random timeouts,
    // check if read buffer is in order and consistent
    #[test]
    fn random_writes_timeouts() {
        const NUM_WRITES: u32 = 100_000;
        const RAW_STORAGE_CAP: usize = 8;
        // Rounded to nearest power of 2 below
        const STORAGE_CAP: usize = 8;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        let num_read_r = Arc::new(AtomicU32::new(0));
        let num_read_w = num_read_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [MaybeUninit::uninit(); RAW_STORAGE_CAP];
                let mut buf = writer::RaceBuffer::new(&mut storage[..], true).unwrap();
                assert!(buf.capacity() == STORAGE_CAP as u32);
                let buf_ptr = &buf as *const writer::RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();
                let mut rng = rand::thread_rng();
                let mut last_prefix = false;
                for i in 0..NUM_WRITES {
                    while i - num_read_w.load(Ordering::SeqCst) >= buf.get_seqn_mod() - 1 {}
                    if last_prefix {
                        buf.write(OrderedEntry::from_index_suffix(i));
                        last_prefix = false;
                    } else {
                        if rng.gen::<f64>() < 0.33 {
                            buf.write(OrderedEntry::from_index_prefix(i));
                            last_prefix = true;
                        } else {
                            buf.write(OrderedEntry::from_index(i));
                        }
                    }
                    let sleep_time: u64 = rng.gen::<u64>() % 1000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const writer::RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper::new(buf_ptr);

                let mut rbuf = Vec::new();
                let mut buf_reader = reader::RaceBufferReader::new(snapper, STORAGE_CAP as u32);

                let mut rng = rand::thread_rng();
                // Last write could be a prefix, only ensure read up to second to last write
                while rbuf.len() < (NUM_WRITES - 1) as usize {
                    buf_reader.read(&mut rbuf).unwrap();
                    num_read_r.store(rbuf.len() as u32, Ordering::SeqCst);
                    let sleep_time: u64 = rng.gen::<u64>() % 3000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                thread::sleep(Duration::from_millis(100));
                buf_reader.read(&mut rbuf).unwrap();
                assert!(
                    (rbuf.len() == NUM_WRITES as usize)
                        || (rbuf.len() == (NUM_WRITES - 1) as usize)
                );
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
                assert!(OrderedEntry::double_entries_consistent(&rbuf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }
}
