#![cfg_attr(not(feature = "std"), no_std)]

use core::cmp::PartialEq;
use core::marker::Copy;
#[cfg(feature = "std")]
use core::marker::PhantomData;

#[cfg(not(feature = "std"))]
use core::fmt;
#[cfg(feature = "std")]
use std::fmt;

pub trait Entry: Copy + PartialEq {
    const NIL_VAL: Self;
    fn is_prefix(&self) -> bool;
}

pub trait Snapper<E>
where
    E: Entry,
{
    fn snap_wcurs(&self) -> usize;
    fn snap_storage(&self, index: usize) -> E;
}

pub struct SizeError();

impl fmt::Debug for SizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Storage size must be a power of 2")
    }
}

#[inline]
/// Returns the corresponding index in backing storage of given cursor index
fn get_cursor_index(storage_cap: usize, cursor: usize) -> usize {
    // Index is lowest n bits of cursor where storage_cap is 2^n
    cursor & (storage_cap - 1)
}
#[repr(C)]
/// Struct used to write to buffer
pub struct RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Writer's cursor
    wcurs: usize,
    /// Backing storage
    storage: &'a mut [E],
}

impl<'a, E> RaceBuffer<'a, E>
where
    E: Entry,
{
    /// Create new RaceBuffer. Returns error if storage size is not power of 2
    pub fn new(storage: &'a mut [E]) -> Result<RaceBuffer<'a, E>, SizeError> {
        let exp = storage.len().trailing_zeros();
        if storage.len() != 1usize << exp {
            return Err(SizeError());
        }

        Ok(RaceBuffer { wcurs: 0, storage })
    }

    /// Write single entry to buffer
    pub fn write(&mut self, data: E) {
        let write_offset = get_cursor_index(self.storage.len(), self.wcurs);
        if self.wcurs > 0 {
            let before_offset = get_cursor_index(self.storage.len(), self.wcurs - 1);
            if self.storage[before_offset] == E::NIL_VAL {
                // Previous write left free nil value behind wcurs
                self.storage[before_offset] = data;
                return;
            }
        }

        if self.storage[write_offset] != E::NIL_VAL && self.storage[write_offset].is_prefix() {
            // Overwriting double entry, must first overwrite suffix
            let suffix_offset = get_cursor_index(self.storage.len(), self.wcurs + 1);
            self.storage[suffix_offset] = E::NIL_VAL;
            self.storage[write_offset] = E::NIL_VAL;
            self.wcurs += 2;
        } else {
            self.storage[write_offset] = E::NIL_VAL;
            self.wcurs += 1;
        }
        self.storage[write_offset] = data;
    }

    /// Get value of backing storage corresponding to given cursor
    pub fn read_storage(&self, curs: usize) -> E {
        self.storage[get_cursor_index(self.storage.len(), curs)]
    }

    /// Get current value of write cursor
    pub fn read_wcurs(&self) -> usize {
        self.wcurs
    }
}

#[cfg(feature = "std")]
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
    phantom: PhantomData<E>,
}

#[cfg(feature = "std")]
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
            phantom: PhantomData,
        }
    }

    /// Attempt to read all new entries in race buffer into given read buffer
    pub fn read(&mut self, rbuf: &mut Vec<E>) {
        let pre_wcurs = self.snapper.snap_wcurs();
        if pre_wcurs > self.storage_cap + self.rcurs {
            // If writer has overwritten unread entries, store nils and correct rcurs
            let num_missed = pre_wcurs - (self.rcurs + self.storage_cap);
            self.store_nil(num_missed, rbuf);
            self.rcurs = pre_wcurs - self.storage_cap;
        }

        // Perform reads into snapshot buffer
        let first_read = self.rcurs;
        let mut buf_snapshot: Vec<E> = Vec::new();
        while self.rcurs < pre_wcurs {
            let storage_index = get_cursor_index(self.storage_cap, self.rcurs);
            buf_snapshot.push(self.snapper.snap_storage(storage_index));
            self.rcurs += 1;
        }

        // Calculate number of entries in snapshot buffer that may have been overwritten
        let post_wcurs = self.snapper.snap_wcurs();
        let overlap = if post_wcurs > self.storage_cap + first_read {
            (post_wcurs - self.storage_cap) - first_read
        } else {
            0
        };
        if overlap >= buf_snapshot.len() {
            // All entries may have been overwritten, return
            self.store_nil(buf_snapshot.len(), rbuf);
            return;
        }
        self.store_nil(overlap, rbuf);
        let mut valid_snapshot = &mut buf_snapshot[overlap..];

        let last_index = valid_snapshot.len() - 1;
        if valid_snapshot.len() >= 2 && valid_snapshot[last_index - 1] == E::NIL_VAL {
            // Writer was possibly not finished writing last two entries, roll
            // back read by 2
            valid_snapshot = &mut valid_snapshot[..last_index - 1];
            self.rcurs -= 2;
        } else if valid_snapshot[last_index] == E::NIL_VAL {
            // Writer was possibly not finished writing last entry,
            // roll back read by 1
            valid_snapshot = &mut valid_snapshot[..last_index];
            self.rcurs -= 1;
        }

        // Store valid entries in read buffer
        for entry in valid_snapshot {
            self.store(*entry, rbuf);
        }
    }

    /// Store given entry in given read buffer,
    /// replacing stored prefixes with nil if suffix is nil
    fn store(&mut self, entry: E, rbuf: &mut Vec<E>) {
        if entry == E::NIL_VAL {
            let last_entry_opt = rbuf.pop();
            match last_entry_opt {
                None => rbuf.push(E::NIL_VAL),
                Some(last_entry) => {
                    if last_entry.is_prefix() {
                        // Suffix lost, replace prefix with nil
                        rbuf.push(E::NIL_VAL);
                        rbuf.push(E::NIL_VAL);
                    } else {
                        rbuf.push(last_entry);
                        rbuf.push(E::NIL_VAL);
                    }
                }
            }
        } else {
            rbuf.push(entry);
        }
    }

    #[inline]
    /// Store given number of nil entries in given read buffer
    fn store_nil(&mut self, num: usize, rbuf: &mut Vec<E>) {
        for _ in 0..num {
            self.store(E::NIL_VAL, rbuf);
        }
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
pub mod tests {
    use super::*;

    use crossbeam;
    use rand::Rng;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;

    #[derive(Clone, Copy, PartialEq)]
    #[repr(transparent)]
    pub struct OrderedEntry(u32);

    impl Entry for OrderedEntry {
        const NIL_VAL: OrderedEntry = OrderedEntry(0);

        fn is_prefix(&self) -> bool {
            self.0 > Self::PREFIX_TAG
        }
    }

    impl OrderedEntry {
        const PREFIX_TAG: u32 = 0x80000000; // 2^31
        const SUFFIX_TAG: u32 = 0x40000000; // 2^30

        pub(crate) fn to_raw(&self) -> u32 {
            if self.is_suffix() {
                self.0 - Self::SUFFIX_TAG
            } else if self.is_prefix() {
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

        pub(crate) fn is_suffix(&self) -> bool {
            self.0 >= Self::SUFFIX_TAG && self.0 < Self::PREFIX_TAG
        }

        // Invariant: Check if entries all have correct index
        fn entries_correct_index(rbuf: &[OrderedEntry]) -> bool {
            for i in 0..rbuf.len() {
                if rbuf[i].to_raw() != i as u32 + 1 && rbuf[i] != Self::NIL_VAL {
                    return false;
                }
            }
            return true;
        }

        // Invariant: Check if entries all have correct index
        fn double_entries_consistent(rbuf: &[OrderedEntry]) -> bool {
            for i in 0..(rbuf.len() - 1) {
                let cur = &rbuf[i];
                let next = &rbuf[i + 1];
                if (cur.is_prefix() && !next.is_suffix()) || (!cur.is_prefix() && next.is_suffix())
                {
                    return false;
                }
            }
            return true;
        }
    }

    pub struct RawPtrSnapper<'a>(*const RaceBuffer<'a, OrderedEntry>);

    impl Snapper<OrderedEntry> for RawPtrSnapper<'_> {
        fn snap_wcurs(&self) -> usize {
            unsafe { self.0.as_ref().unwrap().read_wcurs() }
        }

        fn snap_storage(&self, index: usize) -> OrderedEntry {
            unsafe { self.0.as_ref().unwrap().read_storage(index) }
        }
    }

    #[test]
    // Perform many reads and writes concurrently,
    // check if read buffer is in order and consistent
    fn test_basic() {
        const NUM_WRITES: u32 = 160;
        const STORAGE_CAP: usize = 16;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [OrderedEntry::NIL_VAL; STORAGE_CAP];

                let mut buf = RaceBuffer::new(&mut storage[..]).unwrap();
                let buf_ptr = &buf as *const RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();

                for i in 1..=NUM_WRITES {
                    buf.write(OrderedEntry::from_index(i));
                    std::thread::sleep(Duration::from_millis(10));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap() as *const RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper(buf_ptr);
                let mut rbuf = Vec::new();
                let mut reader = RaceBufferReader::new(snapper, STORAGE_CAP);

                while rbuf.len() < NUM_WRITES as usize {
                    reader.read(&mut rbuf);
                    thread::sleep(Duration::from_millis(10));
                }
                thread::sleep(Duration::from_millis(100));
                reader.read(&mut rbuf);
                assert_eq!(rbuf.len(), NUM_WRITES as usize);
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }

    #[test]
    // Perform many reads and writes concurrently with random timeouts,
    // check if read buffer is in order and consistent
    fn test_random() {
        const NUM_WRITES: u32 = 100_000;
        const STORAGE_CAP: usize = 4;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [OrderedEntry::NIL_VAL; STORAGE_CAP];

                let mut buf = RaceBuffer::new(&mut storage[..]).unwrap();
                let buf_ptr = &buf as *const RaceBuffer<'_, OrderedEntry> as usize;
                ptr_s.send(buf_ptr).unwrap();

                let mut rng = rand::thread_rng();
                let mut last_prefix = false;
                for i in 1..=NUM_WRITES {
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
                let buf_ptr = ptr_r.recv().unwrap() as *const RaceBuffer<'_, OrderedEntry>;
                let snapper = RawPtrSnapper(buf_ptr);

                let mut rbuf = Vec::new();
                let mut reader = RaceBufferReader::new(snapper, STORAGE_CAP);

                let mut rng = rand::thread_rng();
                while rbuf.len() < NUM_WRITES as usize {
                    reader.read(&mut rbuf);
                    let sleep_time: u64 = rng.gen::<u64>() % 3000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                thread::sleep(Duration::from_millis(100));
                reader.read(&mut rbuf);
                assert_eq!(rbuf.len(), NUM_WRITES as usize);
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
                assert!(OrderedEntry::double_entries_consistent(&rbuf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }
}
