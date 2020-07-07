#![cfg_attr(not(feature = "std"), no_std)]

use core::cmp::PartialEq;
use core::marker::Copy;

/// Entry that can be stored in RaceBuffer
pub trait Entry: Copy + PartialEq {
    /// Return true if entry is the first in a double entry
    fn is_prefix(&self) -> bool;
}

/// Returns the corresponding index in backing storage of given cursor index
#[inline]
fn get_cursor_index(storage_cap: usize, cursor: usize, use_base_2_indexing: bool) -> usize {
    if use_base_2_indexing {
        // Index is lowest n bits of cursor where storage_cap is 2^n
        cursor & (storage_cap - 1)
    } else {
        cursor % storage_cap
    }
}

pub mod writer;

#[cfg(feature = "std")]
pub mod reader;

#[cfg(feature = "std")]
#[cfg(test)]
pub mod tests {
    use super::*;

    use core::mem::MaybeUninit;
    use crossbeam;
    use rand::Rng;
    use std::error::Error;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;

    #[derive(Clone, Copy, PartialEq)]
    #[repr(transparent)]
    pub struct OrderedEntry(u32);

    impl Entry for OrderedEntry {
        fn is_prefix(&self) -> bool {
            assert!(!self.is_suffix());
            self.is_prefix_unchecked()
        }
    }

    impl OrderedEntry {
        const PREFIX_TAG: u32 = 0x80000000; // 2^31
        const SUFFIX_TAG: u32 = 0x40000000; // 2^30

        pub(crate) fn to_index(&self) -> u32 {
            if self.is_suffix() {
                self.0 - Self::SUFFIX_TAG
            } else if self.is_prefix_unchecked() {
                self.0 - Self::PREFIX_TAG
            } else {
                self.0
            }
        }

        pub(crate) fn from_index(i: u32) -> Self {
            assert!(i <= Self::SUFFIX_TAG);
            OrderedEntry(i)
        }

        pub(crate) fn from_index_prefix(i: u32) -> Self {
            assert!(i <= Self::SUFFIX_TAG);
            OrderedEntry(i + Self::PREFIX_TAG)
        }

        pub(crate) fn from_index_suffix(i: u32) -> Self {
            assert!(i <= Self::SUFFIX_TAG);
            OrderedEntry(i + Self::SUFFIX_TAG)
        }

        pub(crate) fn is_prefix_unchecked(&self) -> bool {
            self.0 >= Self::PREFIX_TAG
        }

        pub(crate) fn is_suffix(&self) -> bool {
            self.0 >= Self::SUFFIX_TAG && self.0 < Self::PREFIX_TAG
        }

        // Invariant: Check if entries all have correct index
        fn entries_correct_index(rbuf: &[Option<OrderedEntry>]) -> bool {
            for (idx, entry) in rbuf.iter().enumerate().filter(|(_, e)| e.is_some()) {
                if entry.unwrap().to_index() != idx as u32 {
                    return false;
                }
            }
            return true;
        }

        // Invariant: Check if entries all have correct index
        fn double_entries_consistent(rbuf: &[Option<OrderedEntry>]) -> bool {
            if rbuf.len() == 0 {
                return true;
            }
            if let Some(first_entry) = rbuf[0] {
                if first_entry.is_suffix() {
                    return false;
                }
            }
            if let Some(last_entry) = rbuf.last().unwrap() {
                if last_entry.is_prefix_unchecked() {
                    return false;
                }
            }
            for i in 0..(rbuf.len() - 1) {
                match rbuf[i] {
                    None => {
                        if let Some(next) = rbuf[i + 1] {
                            if next.is_suffix() {
                                return false;
                            }
                        }
                    }
                    Some(current) => {
                        if current.is_prefix_unchecked() {
                            if let Some(next) = rbuf[i + 1] {
                                if !next.is_suffix() {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        }
                    }
                }
            }
            return true;
        }
    }

    pub struct RawPtrSnapper<'a>(*const writer::RaceBuffer<'a, OrderedEntry>);

    impl reader::Snapper<OrderedEntry> for RawPtrSnapper<'_> {
        fn snap_wcurs(&self) -> Result<usize, Box<dyn Error>> {
            unsafe { Ok(self.0.as_ref().unwrap().read_wcurs()) }
        }

        fn snap_owcurs(&self) -> Result<usize, Box<dyn Error>> {
            unsafe { Ok(self.0.as_ref().unwrap().read_owcurs()) }
        }

        fn snap_storage(&self, index: usize) -> Result<OrderedEntry, Box<dyn Error>> {
            unsafe { Ok(self.0.as_ref().unwrap().read_storage(index)) }
        }
    }

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

                let mut buf = writer::RaceBuffer::new(&mut storage[..], false).unwrap();
                assert!(buf.get_slice().len() == STORAGE_CAP);
                let buf_ptr = &buf as *const writer::RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();

                for i in 0..NUM_WRITES {
                    buf.write(OrderedEntry::from_index(i));
                    std::thread::sleep(Duration::from_millis(10));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const writer::RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper(buf_ptr);
                let mut rbuf = Vec::new();
                let mut buf_reader = reader::RaceBufferReader::new(snapper, STORAGE_CAP);

                while rbuf.len() < NUM_WRITES as usize {
                    buf_reader.read(&mut rbuf).unwrap();
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
    fn test_random() {
        const NUM_WRITES: u32 = 100_000;
        const RAW_STORAGE_CAP: usize = 7;
        // Rounded to nearest power of 2 below
        const STORAGE_CAP: usize = 4;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [MaybeUninit::uninit(); RAW_STORAGE_CAP];
                let mut buf = writer::RaceBuffer::new(&mut storage[..], true).unwrap();
                assert!(buf.get_slice().len() == STORAGE_CAP);
                let buf_ptr = &buf as *const writer::RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();
                let mut rng = rand::thread_rng();
                let mut last_prefix = false;
                for i in 0..NUM_WRITES {
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
                let snapper = RawPtrSnapper(buf_ptr);

                let mut rbuf = Vec::new();
                let mut buf_reader = reader::RaceBufferReader::new(snapper, STORAGE_CAP);

                let mut rng = rand::thread_rng();
                // Last write could be a prefix, only ensure read up to second to last write
                while rbuf.len() < (NUM_WRITES - 1) as usize {
                    buf_reader.read(&mut rbuf).unwrap();
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

    /// Test backing storage size rounding and minimum size enforcement
    #[test]
    fn test_init_sizes() {
        // Ensure minimum storage size is checked
        let mut too_small_storage =
            [MaybeUninit::<OrderedEntry>::uninit(); writer::MIN_STORAGE_CAP - 1];
        assert!(writer::RaceBuffer::new(&mut too_small_storage[..], false).is_err());
        assert!(writer::RaceBuffer::new(&mut too_small_storage[..], true).is_err());

        let input_sizes = [5, 6, 7, 8, 9, 12, 16];

        let output_sizes: Vec<usize> = input_sizes
            .iter()
            .map(|size| {
                let mut storage = vec![MaybeUninit::<OrderedEntry>::uninit(); *size];
                writer::RaceBuffer::new(&mut storage[..], false)
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
                writer::RaceBuffer::new(&mut storage[..], true)
                    .unwrap()
                    .get_slice()
                    .len()
            })
            .collect();
        assert_eq!(&[4, 4, 4, 8, 8, 8, 16][..], &rounded_output_sizes[..]);
    }
}
