#![cfg_attr(not(feature = "std"), no_std)]

use core::cmp::PartialEq;
use core::marker::Copy;

/// Returns the corresponding index in backing storage to given sequence number
#[inline]
fn get_seqn_index(storage_cap: usize, seqn: u64, use_base_2_indexing: bool) -> usize {
    // Cast to usize safe because index in storage slice cannot be greater than usize
    if use_base_2_indexing {
        // Index is lowest n bits of seqn where storage_cap is 2^n
        (seqn & (storage_cap as u64 - 1)) as usize
    } else {
        (seqn % storage_cap as u64) as usize
    }
}

/// Calculate the number of entries missed based on the read and overwrite sequence numbers
#[inline]
fn num_missed(read_seqn: u64, overwrite_seqn: u64) -> u64 {
    if overwrite_seqn < read_seqn {
        0
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
pub mod tests {
    use super::*;

    use core::mem::MaybeUninit;
    use crossbeam;
    use rand::Rng;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;

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
