//! FencedRingBuffer, a single producer, single consumer, shared memory ring
//! buffer which maintains consistency while operating under race conditions.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]

use core::marker::Copy;
use core::ops::{Add, AddAssign, Sub};
use core::sync::atomic::{fence, Ordering};

/// The index of an entry in the sequence of all entries written to the buffer
/// Note: This struct is 2 separate 32 bit words so they can be read in one cpu
/// instruction on 32 bit machines, for asynchronous reading. It is public so it
/// can be directly accessed from the asynchronous reader.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[repr(C)]
pub struct SeqNum {
    /// High 32 bits of sequence number
    pub high: u32,
    /// Low 32 bits of sequence number
    pub low: u32,
}

impl SeqNum {
    const UPDATING_HIGH_MASK: u32 = 0b1000_0000_0000_0000_0000_0000_0000_0000;

    pub(crate) fn new(high: u32, low: u32) -> Self {
        debug_assert!(high < Self::UPDATING_HIGH_MASK);
        Self { high, low }
    }

    #[cfg(feature = "std")]
    pub(crate) fn has_updating_high_bit_set(high: u32) -> bool {
        high & Self::UPDATING_HIGH_MASK != 0
    }

    /// Set the high bit of the high word so the asynchronous reader does not
    /// try to use the sequence number in an inconsistent state
    fn set_updating_high_bit(&mut self) {
        self.high |= Self::UPDATING_HIGH_MASK;
    }

    /// Increment the sequence number by the given amount, using an "updating"
    /// flag to ensure the asynchronous reader does not use the sequence
    /// number in an inconsistent state
    pub(crate) fn increment(&mut self, n: Self) {
        let (new_low, overflowed) = self.low.overflowing_add(n.low);
        let high_increment = n.high + if overflowed { 1 } else { 0 };
        if high_increment > 0 {
            let new_high = self.high + high_increment;
            // Set the updating bit before modifying the value of the sequence number.
            // While this bit is set, the reader will retry reading the high word.
            // Fences are used to prevent write reorders
            self.set_updating_high_bit();
            fence(Ordering::Release);
            self.low = new_low;
            fence(Ordering::Release);
            self.high = new_high;
        } else {
            self.low = new_low;
        }
        fence(Ordering::Release);
    }
}

impl From<SeqNum> for u64 {
    fn from(s: SeqNum) -> u64 {
        debug_assert!(s.high < SeqNum::UPDATING_HIGH_MASK);
        ((s.high as u64) << 32) + s.low as u64
    }
}

impl From<u64> for SeqNum {
    fn from(n: u64) -> Self {
        let high = (n >> 32) as u32;
        debug_assert!(high < Self::UPDATING_HIGH_MASK);
        Self {
            high,
            low: n as u32,
        }
    }
}

impl Add<Self> for SeqNum {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        (u64::from(self) + u64::from(rhs)).into()
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
        (u64::from(self) - u64::from(rhs)).into()
    }
}

impl Add<u64> for SeqNum {
    type Output = Self;

    fn add(self, rhs: u64) -> Self::Output {
        (u64::from(self) + rhs).into()
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
        (u64::from(self) - rhs).into()
    }
}

/// Returns the corresponding index in backing storage to given sequence number
#[inline]
fn get_seqn_index(storage_cap: usize, seqn: SeqNum, use_base_2_indexing: bool) -> usize {
    // Cast to usize safe because index in storage slice cannot be greater than
    // usize
    if use_base_2_indexing {
        // Index is lowest n bits of seqn where storage_cap is 2^n
        (u64::from(seqn) & (storage_cap as u64 - 1)) as usize
    } else {
        (u64::from(seqn) % storage_cap as u64) as usize
    }
}

/// Calculate the number of entries missed based on the read and overwrite
/// sequence numbers
#[inline]
fn num_missed(read_seqn: SeqNum, overwrite_seqn: SeqNum) -> SeqNum {
    if overwrite_seqn < read_seqn {
        0.into()
    } else {
        overwrite_seqn - read_seqn
    }
}

/// Entry that can be stored in a FencedRingBuffer
pub trait Entry: Copy + PartialEq {
    /// Return true if the entry is the first in a pair of entries
    /// that precede either one or two further entries.  Whether
    /// there are three or four entries connected depends on if
    /// the third entry `is_prefix`
    ///
    /// Possible valid patterns of entries:
    /// * `[non-prefix opaque content]`
    /// * `[prefix, opaque content]`
    /// * `[mega-prefix, opaque content, non-prefix opaque content]`
    /// * `[mega-prefix, opaque content, prefix, opaque content]`
    fn is_mega_variable_prefix(&self) -> bool;
    /// Return true if entry is the first in at least a double entry
    fn is_prefix(&self) -> bool;

    /// Return true if entry definitely requires exactly one
    /// following entry to be complete enough to understand.
    fn is_fixed_size_prefix(&self) -> bool {
        self.is_prefix() && !self.is_mega_variable_prefix()
    }
}

/// An entry or double entry that has just been overwritten.
#[cfg_attr(target_pointer_width = "32", repr(align(32)))]
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum WholeEntry<E>
where
    E: Entry,
{
    /// Single entry overwritten
    Single(E),
    /// Double entry overwritten
    Double(E, E),
    /// Triple entry overwritten (a mega-prefix, its content, then followed by a non-prefix entry)
    Triple(E, E, E),
    /// Quad entry overwritten (a mega-prefix, its content, a prefix entry, then followed by a non-prefix entry)
    Quad(E, E, E, E),
}

impl<E> WholeEntry<E>
where
    E: Entry,
{
    /// 1 if entry is single, 2 if double, and so on
    pub fn size(&self) -> u8 {
        match self {
            Self::Single(_) => 1,
            Self::Double(_, _) => 2,
            WholeEntry::Triple(_, _, _) => 3,
            WholeEntry::Quad(_, _, _, _) => 4,
        }
    }

    /// Returns the entry if single, or the first entry if a double
    pub fn first_entry(&self) -> &E {
        match self {
            Self::Single(e) => e,
            Self::Double(e, _) => e,
            Self::Triple(e, _, _) => e,
            Self::Quad(e, _, _, _) => e,
        }
    }
}

#[cfg(feature = "std")]
pub mod async_reader;

pub mod buffer;
pub use buffer::FencedRingBuffer;

#[cfg(all(feature = "std", test))]
mod test_support;

#[cfg(all(feature = "std", test))]
pub mod tests {
    use super::*;

    use crate::buffer::MIN_STORAGE_CAP;
    use core::mem::MaybeUninit;
    use crossbeam;
    use proptest::prelude::*;
    use rand::Rng;
    use std::sync::{Arc, Barrier};
    use std::time::Duration;
    use test_support::{ErrorPronePtrSnapper, OrderedEntry, OutputOrderedEntry, PtrSnapper};

    prop_compose! {
        fn gen_half_full_seq_num()(
            // Half the max so we can add two full values together without
            // overflowing into the reserved high bit
            high in 0_u32..(SeqNum::UPDATING_HIGH_MASK / 2),
            low in proptest::num::u32::ANY
        ) -> SeqNum {
            assert!(!SeqNum::has_updating_high_bit_set(high));
            SeqNum::new(high, low)
        }
    }

    prop_compose! {
        fn gen_seq_num()(
            high in 0_u32..SeqNum::UPDATING_HIGH_MASK,
            low in proptest::num::u32::ANY
        ) -> SeqNum {
            assert!(!SeqNum::has_updating_high_bit_set(high));
            SeqNum::new(high, low)
        }
    }

    proptest! {
        #[test]
        fn num_missed_entries(read_seqn in gen_seq_num(), overwrite_seqn in gen_seq_num()) {
            let read_seqn_raw = u64::from(read_seqn);
            let overwrite_seqn_raw = u64::from(overwrite_seqn);
            let num_missed_seqn = num_missed(read_seqn, overwrite_seqn);
            if overwrite_seqn_raw < read_seqn_raw {
                prop_assert_eq!(u64::from(num_missed_seqn), 0);
            } else {
                prop_assert!(u64::from(num_missed_seqn) <= overwrite_seqn_raw);
            }
        }
    }

    proptest! {
        #[test]
        fn seqn_indexing(storage_cap in MIN_STORAGE_CAP..=usize::MAX, seqn in gen_seq_num()) {
            let use_base_2_indexing = false;
            let index = get_seqn_index(storage_cap, seqn, use_base_2_indexing);
            prop_assert!(index < storage_cap);
            let use_base_2_indexing = true;
            let index = get_seqn_index(storage_cap, seqn, use_base_2_indexing);
            prop_assert!(index < storage_cap);
        }
    }

    #[test]
    fn seq_nums() {
        assert_eq!(SeqNum::new(u32::MAX >> 1, u32::MAX), (u64::MAX >> 1).into());
        assert_eq!(
            u64::from(SeqNum::new(u32::MAX >> 1, u32::MAX)),
            u64::MAX >> 1
        );
        assert_eq!(
            SeqNum::new(u32::MAX >> 1, 0),
            (0b01111111_11111111_11111111_11111111_00000000_00000000_00000000_00000000).into()
        );
        assert_eq!(
            u64::from(SeqNum::new(u32::MAX >> 1, 0)),
            0b01111111_11111111_11111111_11111111_00000000_00000000_00000000_00000000
        );

        assert_eq!(
            SeqNum::new(1, 2) + SeqNum::new(2, u32::MAX),
            SeqNum::new(4, 1)
        );
        assert_eq!(
            SeqNum::new(1, 2) + (u32::MAX as u64 * 3 + 2),
            SeqNum::new(4, 1)
        );
        assert_eq!(SeqNum::new(0, 0) + SeqNum::new(0, 0), SeqNum::new(0, 0));

        assert!(SeqNum::new(1, 0) > SeqNum::new(0, 2));
        assert!(SeqNum::new(1, 3) > SeqNum::new(1, 2));

        proptest!(
            ProptestConfig::default(),
            |(high in 0_u32..SeqNum::UPDATING_HIGH_MASK, low in proptest::num::u32::ANY)| {
                prop_assert!(!SeqNum::has_updating_high_bit_set(high));
                let seqnum = SeqNum::new(high, low);
                prop_assert_eq!(u64::from(seqnum), (high as u64) << 32 | (low as u64));
            }
        );

        proptest!(
            ProptestConfig::default(),
            |(mut a in gen_half_full_seq_num(), b in gen_half_full_seq_num())| {
                let a_raw = u64::from(a);
                let b_raw = u64::from(b);
                a.increment(b);
                prop_assert_ne!(a, b);
                prop_assert!(a > b);
                prop_assert_eq!(u64::from(a), a_raw + b_raw);
            }
        );

        proptest!(
            ProptestConfig::default(),
            |(low in 1..=u32::MAX)| {
                let mut a = SeqNum::new(0, u32::MAX);
                let b = SeqNum::new(0, low);
                a.increment(b);
                prop_assert!(a.high > b.high);
                prop_assert_ne!(a.low, b.low);
                prop_assert!(a > b);
            }
        );

        proptest!(
            ProptestConfig::default(),
            |(seqnum in gen_seq_num())| {
                let mut a = seqnum.clone();
                a.set_updating_high_bit();
                prop_assert_ne!(a, seqnum);
                prop_assert!(SeqNum::has_updating_high_bit_set(a.high));
            }
        );
    }

    // Perform many writes and reads concurrently,
    // check if reader output is in order and consistent
    proptest! {
        #[test]
        fn async_output(
            num_writes in 1_u32..=1024_u32,
            storage_cap in 4_usize..=512_usize,
        ) {
            let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
            let barr_r = Arc::new(Barrier::new(2));
            let barr_w = barr_r.clone();
            crossbeam::thread::scope(|s| {
                s.spawn(move |_| {
                    let mut storage = vec![MaybeUninit::uninit(); storage_cap];

                    let mut buf = FencedRingBuffer::new(&mut storage[..], false).unwrap();
                    assert!(buf.capacity() == storage_cap);
                    let buf_ptr = &buf as *const FencedRingBuffer<'_, OrderedEntry> as usize;
                    ptr_s.send(buf_ptr).unwrap();

                    for i in 0..num_writes {
                        buf.push(OrderedEntry::from_index(i));
                    }
                    barr_r.wait();
                });
                s.spawn(move |_| {
                    let buf_ptr = ptr_r.recv().unwrap() as *const FencedRingBuffer<'_, OrderedEntry>;
                    let snapper = PtrSnapper::new(buf_ptr);
                    let mut output_buf = Vec::new();
                    let mut buf_reader = async_reader::FencedReader::new(snapper, storage_cap);

                    let mut total_items_read = 0;
                    while total_items_read < num_writes as usize {
                        let mut temp_buf = Vec::new();
                        let n_missed = buf_reader.read(&mut temp_buf).unwrap();
                        total_items_read += n_missed as usize + temp_buf.len();

                        output_buf.push(OutputOrderedEntry::Missed(n_missed));
                        output_buf.extend(temp_buf.iter().map(|e| OutputOrderedEntry::Present(*e)));
                    }
                    OutputOrderedEntry::check_entries_correct_index(&output_buf[..]);
                    barr_w.wait();
                });
            })
            .unwrap();
        }
    }

    // Perform many reads and writes concurrently with random timeouts, and random
    // snapshot errors check if read buffer is in order and consistent
    proptest! {
        #[test]
        fn async_output_timeouts_and_errors(
            num_writes in 2_u32..=1024_u32,
            writer_sleep_time_ns in 0_u64..=1000_u64,
            reader_sleep_time_ns in 0_u64..=3000_u64,
        ) {
            const STORAGE_CAP: usize = 8;

            let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
            let barr_r = Arc::new(Barrier::new(2));
            let barr_w = barr_r.clone();
            crossbeam::thread::scope(|s| {
                s.spawn(move |_| {
                    let mut storage = [MaybeUninit::uninit(); STORAGE_CAP];
                    let mut buf = FencedRingBuffer::new(&mut storage[..], true).unwrap();
                    assert!(buf.capacity() == STORAGE_CAP);
                    let buf_ptr = &buf as *const FencedRingBuffer<'_, OrderedEntry> as usize;
                    ptr_s.send(buf_ptr).unwrap();
                    let mut rng = rand::thread_rng();
                    let mut last_prefix = false;

                    for i in 0..num_writes {
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
                        std::thread::sleep(Duration::from_nanos(writer_sleep_time_ns));
                    }
                    barr_r.wait();
                });
                s.spawn(move |_| {
                    let buf_ptr = ptr_r.recv().unwrap() as *const FencedRingBuffer<'_, OrderedEntry>;
                    let snapper = ErrorPronePtrSnapper::new(buf_ptr);
                    let mut output_buf = Vec::new();
                    let mut buf_reader = async_reader::FencedReader::new(snapper, STORAGE_CAP);

                    let mut total_items_read = 0;
                    while total_items_read < (num_writes - 1) as u64 {
                        let mut temp_buf = Vec::new();
                        if let Ok(n_missed) = buf_reader.read(&mut temp_buf) {
                            let n_read: u64 = temp_buf.iter().map(|whole| whole.size() as u64).sum();
                            total_items_read += n_missed + n_read;

                            output_buf.push(OutputOrderedEntry::Missed(n_missed));
                            output_buf.extend(temp_buf.iter().map(|e| OutputOrderedEntry::Present(*e)));
                        }

                        std::thread::sleep(Duration::from_nanos(reader_sleep_time_ns));
                    }
                    OutputOrderedEntry::check_entries_correct_index(&output_buf[..]);
                    OutputOrderedEntry::check_double_entries_consistent(&output_buf[..]);
                    barr_w.wait();
                });
            })
            .unwrap();
        }
    }
}
