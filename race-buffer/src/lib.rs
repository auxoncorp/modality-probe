//! RaceBuffer, a single producer, single consumer, shared memory ring buffer which maintains
//! consistency while operating under race conditions.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]

use core::marker::Copy;
use core::ops::{Add, Sub, AddAssign};
use core::sync::atomic::{fence, Ordering};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[repr(C)]
pub(crate) struct SeqNum {
    high: u32,
    low: u32,
}

impl SeqNum {
    const UPDATING_EPOCH_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;

    #[cfg(feature = "std")]
    pub(crate) fn new(high: u32, low: u32) -> Self {
        debug_assert!(high < Self::UPDATING_EPOCH_MASK);
        Self { high, low }
    }

    #[cfg(feature = "std")]
    pub(crate) fn has_updating_high_bit_set(high: u32) -> bool {
        high & Self::UPDATING_EPOCH_MASK != 0
    }

    fn set_updating_high_bit(&mut self) {
        self.high |= Self::UPDATING_EPOCH_MASK;
    }

    pub(crate) fn increment(&mut self, n: Self) {
        let (new_low, overflowed) = self.low.overflowing_add(n.low);
        let high_increment = n.high + if overflowed { 1 } else { 0 };
        if high_increment > 0 {
            let new_high = self.high + high_increment;
            self.set_updating_high_bit();
            fence(Ordering::Release);
            self.low = new_low;
            fence(Ordering::Release);
            self.high = new_high;
            fence(Ordering::Release);
        } else {
            self.low = new_low;
            fence(Ordering::Release);
        }
    }
}

impl Into<u64> for SeqNum {
    fn into(self) -> u64 {
        debug_assert!(self.high < Self::UPDATING_EPOCH_MASK);
        ((self.high as u64) << 32) + self.low as u64
    }
}

impl From<u64> for SeqNum {
    fn from(n: u64) -> Self {
        let high = (n >> 32) as u32;
        debug_assert!(high < Self::UPDATING_EPOCH_MASK);
        Self {
            high,
            low: n as u32,
        }
    }
}

impl Add<Self> for SeqNum {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        (Into::<u64>::into(self) + Into::<u64>::into(rhs)).into()
    }
}

impl AddAssign<Self> for SeqNum {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl Sub<Self> for SeqNum {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        (Into::<u64>::into(self) - Into::<u64>::into(rhs)).into()
    }
}

impl Add<u64> for SeqNum {
    type Output = Self;

    fn add(self, rhs: u64) -> Self::Output {
        (Into::<u64>::into(self) + rhs).into()
    }
}

impl AddAssign<u64> for SeqNum {
    fn add_assign(&mut self, rhs: u64) {
        *self = *self + rhs
    }
}

impl Sub<u64> for SeqNum {
    type Output = Self;

    fn sub(self, rhs: u64) -> Self::Output {
        (Into::<u64>::into(self) - rhs).into()
    }
}

/// Returns the corresponding index in backing storage to given sequence number
#[inline]
fn get_seqn_index(storage_cap: usize, seqn: SeqNum, use_base_2_indexing: bool) -> usize {
    // Cast to usize safe because index in storage slice cannot be greater than usize
    if use_base_2_indexing {
        // Index is lowest n bits of seqn where storage_cap is 2^n
        (Into::<u64>::into(seqn) & (storage_cap as u64 - 1)) as usize
    } else {
        (Into::<u64>::into(seqn) % storage_cap as u64) as usize
    }
}

/// Calculate the number of entries missed based on the read and overwrite sequence numbers
#[inline]
fn num_missed(read_seqn: SeqNum, overwrite_seqn: SeqNum) -> SeqNum {
    if overwrite_seqn < read_seqn {
        0.into()
    } else {
        overwrite_seqn - read_seqn
    }
}

/// Entry that can be stored in a RaceBuffer
pub trait Entry: Copy + PartialEq {
    /// Return true if entry is the first in a double entry
    fn is_prefix(&self) -> bool;
}

#[cfg(feature = "std")]
pub mod async_reader;

pub mod buffer;
pub use buffer::RaceBuffer;

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
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;
    use util::{OrderedEntry, OutputOrderedEntry, RawPtrSnapper};

    // Perform many reads and writes concurrently,
    // check if read buffer is in order and consistent
    #[test]
    fn test_basic() {
        const NUM_WRITES: u32 = 160;
        const STORAGE_CAP: usize = 15;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];

                let mut buf = RaceBuffer::new(&mut storage[..], false).unwrap();
                assert!(buf.capacity() == STORAGE_CAP);
                let buf_ptr = &buf as *const RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();

                for i in 0..NUM_WRITES {
                    buf.push(OrderedEntry::from_index(i));
                    std::thread::sleep(Duration::from_millis(10));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper::new(buf_ptr);
                let mut output_buf = Vec::new();
                let mut buf_reader = async_reader::RaceReader::new(snapper, STORAGE_CAP);

                let mut total_items_read = 0;
                while total_items_read < NUM_WRITES as usize {
                    let mut temp_buf = Vec::new();
                    let n_missed = buf_reader.read(&mut temp_buf).unwrap();
                    total_items_read += n_missed as usize + temp_buf.len();

                    output_buf.push(OutputOrderedEntry::Missed(n_missed));
                    output_buf.extend(temp_buf.iter().map(|e| OutputOrderedEntry::Present(*e)));

                    thread::sleep(Duration::from_millis(10));
                }
                assert!(OutputOrderedEntry::entries_correct_index(&output_buf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }

    // Perform many reads and writes concurrently with random timeouts,
    // check if read buffer is in order and consistent
    #[test]
    fn test_random() {
        const NUM_WRITES: u32 = 100_000;
        const STORAGE_CAP: usize = 8;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
                let mut buf = RaceBuffer::new(&mut storage[..], true).unwrap();
                assert!(buf.capacity() == STORAGE_CAP);
                let buf_ptr = &buf as *const RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();
                let mut rng = rand::thread_rng();
                let mut last_prefix = false;

                for i in 0..NUM_WRITES {
                    if last_prefix {
                        buf.push(OrderedEntry::from_index_suffix(i));
                        last_prefix = false;
                    } else {
                        if rng.gen::<f64>() < 0.33 {
                            buf.push(OrderedEntry::from_index_prefix(i));
                            last_prefix = true;
                        } else {
                            buf.push(OrderedEntry::from_index(i));
                        }
                    }

                    let sleep_time: u64 = rng.gen::<u64>() % 1000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper::new(buf_ptr);
                let mut output_buf = Vec::new();
                let mut buf_reader = async_reader::RaceReader::new(snapper, STORAGE_CAP);
                let mut rng = rand::thread_rng();

                let mut total_items_read = 0;
                while total_items_read < (NUM_WRITES - 1) as usize {
                    let mut temp_buf = Vec::new();
                    let n_missed = buf_reader.read(&mut temp_buf).unwrap();
                    total_items_read += n_missed as usize + temp_buf.len();

                    output_buf.push(OutputOrderedEntry::Missed(n_missed));
                    output_buf.extend(temp_buf.iter().map(|e| OutputOrderedEntry::Present(*e)));

                    let sleep_time: u64 = rng.gen::<u64>() % 3000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                assert!(OutputOrderedEntry::entries_correct_index(&output_buf[..]));
                assert!(OutputOrderedEntry::double_entries_consistent(
                    &output_buf[..]
                ));
                barr_w.wait();
            });
        })
        .unwrap();
    }
}
