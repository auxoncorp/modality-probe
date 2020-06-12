#![cfg_attr(not(feature = "default"), no_std)]

#[inline]
fn get_cursor_index(storage_len: usize, cursor: usize) -> usize {
    cursor & (storage_len - 1)
}
#[repr(C)]
pub struct RaceBuffer<'a, T, H>
where
    T: core::marker::Copy + core::cmp::PartialEq,
    H: Fn(T) -> bool,
{
    wcurs: usize,
    storage: &'a mut [T],
    nil_val: T,
    is_prefix: H,
}

impl<'a, T, H> RaceBuffer<'a, T, H>
where
    T: core::marker::Copy + core::cmp::PartialEq,
    H: Fn(T) -> bool,
{
    pub fn new(storage: &'a mut [T], nil_val: T, is_prefix: H) -> RaceBuffer<'a, T, H> {
        let exp = storage.len().trailing_zeros();
        if storage.len() != 1usize << exp {
            // TODO - add error for non power of 2
            unimplemented!();
        }

        RaceBuffer {
            wcurs: 0,
            storage: storage,
            nil_val: nil_val,
            is_prefix: is_prefix,
        }
    }

    pub fn write(&mut self, data: T) {
        let write_offset = get_cursor_index(self.storage.len(), self.wcurs);
        if self.wcurs > 0 {
            let before_offset = get_cursor_index(self.storage.len(), self.wcurs - 1);
            if self.storage[before_offset] == self.nil_val {
                // previous write left free nil value behind wcurs
                self.storage[before_offset] = data;
                return;
            }
        }

        if self.storage[write_offset] != self.nil_val
            && (self.is_prefix)(self.storage[write_offset])
        {
            let suffix_offset = get_cursor_index(self.storage.len(), self.wcurs + 1);
            self.storage[suffix_offset] = self.nil_val;
            self.storage[write_offset] = self.nil_val;
            self.wcurs += 2;
        } else {
            self.storage[write_offset] = self.nil_val;
            self.wcurs += 1;
        }
        self.storage[write_offset] = data;
    }

    pub fn read_storage(&self, index: usize) -> T {
        self.storage[index]
    }

    pub fn read_wcurs(&self) -> usize {
        self.wcurs
    }
}

#[cfg(feature = "default")]
pub struct RaceBufferReader<T, F, G, H>
where
    T: core::marker::Copy + core::cmp::PartialEq,
    F: Fn() -> usize,
    G: Fn(usize) -> T,
    H: Fn(T) -> bool,
{
    buf_len: usize,
    rcurs: usize,
    read_wcurs: F,
    read_storage: G,
    is_prefix: H,
    nil_val: T,
}

#[cfg(feature = "default")]
impl<T, F, G, H> RaceBufferReader<T, F, G, H>
where
    T: core::marker::Copy + core::cmp::PartialEq,
    F: Fn() -> usize,
    G: Fn(usize) -> T,
    H: Fn(T) -> bool,
{
    pub fn new(
        buf_len: usize,
        read_wcurs: F,
        read_storage: G,
        is_prefix: H,
        nil_val: T,
    ) -> RaceBufferReader<T, F, G, H> {
        RaceBufferReader {
            buf_len: buf_len,
            rcurs: 0,
            read_wcurs: read_wcurs,
            read_storage: read_storage,
            nil_val: nil_val,
            is_prefix: is_prefix,
        }
    }

    pub fn read(&mut self, rbuf: &mut Vec<T>) {
        let pre_wcurs = (self.read_wcurs)();
        if pre_wcurs > self.buf_len + self.rcurs {
            // correct rcurs if writer lapped reader
            let num_missed = pre_wcurs - (self.rcurs + self.buf_len);
            self.store_nil(num_missed, rbuf);
            self.rcurs = pre_wcurs - self.buf_len;
        }

        let first_read = self.rcurs;
        let mut buf_snapshot: Vec<T> = Vec::new();
        while self.rcurs < pre_wcurs {
            let storage_index = get_cursor_index(self.buf_len, self.rcurs);
            buf_snapshot.push((self.read_storage)(storage_index));
            self.rcurs += 1;
        }

        let post_wcurs = (self.read_wcurs)();
        let overlap;
        if post_wcurs > self.buf_len + first_read {
            overlap = (post_wcurs - self.buf_len) - first_read;
        } else {
            overlap = 0;
        }
        if overlap >= buf_snapshot.len() {
            // all entries may have been overwritten, return
            self.store_nil(buf_snapshot.len(), rbuf);
            return;
        }
        self.store_nil(overlap, rbuf);

        let mut valid_snapshot = &mut buf_snapshot[overlap..];
        let last_index = valid_snapshot.len() - 1;
        if valid_snapshot.len() >= 2 && valid_snapshot[last_index - 1] == self.nil_val {
            // writer was possibly not finished writing last two entries, roll back read by 2
            valid_snapshot = &mut valid_snapshot[..last_index - 1];
            self.rcurs -= 2;
        } else if valid_snapshot[last_index] == self.nil_val {
            // writer was possibly not finished writing last entry, roll back read by 1
            valid_snapshot = &mut valid_snapshot[..last_index];
            self.rcurs -= 1;
        }

        for entry in valid_snapshot {
            self.store(*entry, rbuf);
        }
    }

    fn store(&mut self, entry: T, rbuf: &mut Vec<T>) {
        if entry == self.nil_val {
            let last_entry_opt = rbuf.pop();
            match last_entry_opt {
                None => rbuf.push(self.nil_val),
                Some(last_entry) => {
                    if (self.is_prefix)(last_entry) {
                        // suffix lost, replace prefix with nil
                        rbuf.push(self.nil_val);
                        rbuf.push(self.nil_val);
                    } else {
                        rbuf.push(last_entry);
                        rbuf.push(self.nil_val);
                    }
                }
            }
        } else {
            rbuf.push(entry);
        }
    }

    fn store_nil(&mut self, num: usize, rbuf: &mut Vec<T>) {
        for _ in 0..num {
            self.store(self.nil_val, rbuf);
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    use crossbeam;
    use rand::random;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::Duration;

    #[derive(Clone, Copy, PartialEq)]
    #[repr(transparent)]
    pub struct OrderedEntry(u32);

    impl OrderedEntry {
        const PREFIX_TAG: u32 = 2147483648; // 2^31
        const SUFFIX_TAG: u32 = 1073741824; // 2^30
        const NIL_VAL: OrderedEntry = OrderedEntry(0);

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
            if i >= Self::SUFFIX_TAG {
                panic!("Index too high! OrderedEntryop two bits used for tagging double entries")
            } else {
                OrderedEntry(i)
            }
        }

        pub(crate) fn from_index_prefix(i: u32) -> Self {
            if i >= Self::SUFFIX_TAG {
                panic!("Index too high! OrderedEntryop two bits used for tagging double entries")
            } else {
                OrderedEntry(i + Self::PREFIX_TAG)
            }
        }

        pub(crate) fn from_index_suffix(i: u32) -> Self {
            if i >= Self::SUFFIX_TAG {
                panic!("Index too high! OrderedEntryop two bits used for tagging double entries")
            } else {
                OrderedEntry(i + Self::SUFFIX_TAG)
            }
        }

        pub(crate) fn is_prefix(&self) -> bool {
            self.0 > Self::PREFIX_TAG
        }

        pub(crate) fn is_suffix(&self) -> bool {
            self.0 >= Self::SUFFIX_TAG && self.0 < Self::PREFIX_TAG
        }

        // Check if entries all have correct index
        fn entries_correct_index(rbuf: &[OrderedEntry]) -> bool {
            for i in 0..rbuf.len() {
                if rbuf[i].to_raw() != i as u32 + 1 && rbuf[i] != Self::NIL_VAL {
                    return false;
                }
            }
            return true;
        }

        // Check if entries all have correct index
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

    #[test]
    fn test_basic() {
        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [OrderedEntry::NIL_VAL; 16];

                let mut buf = RaceBuffer::new(
                    &mut storage[..],
                    OrderedEntry::NIL_VAL,
                    (|e| e.is_prefix()) as fn(OrderedEntry) -> bool,
                );
                let buf_ptr =
                    &buf as *const RaceBuffer<'_, OrderedEntry, fn(OrderedEntry) -> bool> as usize;
                ptr_s.send(buf_ptr).unwrap();

                for i in 1..=160 {
                    buf.write(OrderedEntry::from_index(i));
                    std::thread::sleep(Duration::from_millis(10));
                }
                std::thread::sleep(Duration::from_secs(1));
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap()
                    as *const RaceBuffer<'_, OrderedEntry, fn(OrderedEntry) -> bool>;
                let mut rbuf = Vec::new();
                let mut reader = RaceBufferReader::new(
                    16,
                    || unsafe { buf_ptr.as_ref().unwrap().read_wcurs() },
                    |i| unsafe { buf_ptr.as_ref().unwrap().read_storage(i) },
                    |e| e.is_prefix(),
                    OrderedEntry::NIL_VAL,
                );

                while rbuf.len() < 160 {
                    reader.read(&mut rbuf);
                    thread::sleep(Duration::from_millis(10));
                }
                thread::sleep(Duration::from_millis(100));
                reader.read(&mut rbuf);
                assert_eq!(rbuf.len(), 160);
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
            });
        })
        .unwrap();
    }

    #[test]
    fn test_random() {
        const NUM_ENTRIES: u32 = 100_000;
        const STORAGE_LEN: usize = 4;

        let (ptr_s, ptr_r) = crossbeam::crossbeam_channel::bounded(0);
        let barr_r = Arc::new(Barrier::new(2));
        let barr_w = barr_r.clone();
        crossbeam::thread::scope(|s| {
            s.spawn(move |_| {
                let mut storage = [OrderedEntry::NIL_VAL; STORAGE_LEN];

                let mut buf = RaceBuffer::new(
                    &mut storage[..],
                    OrderedEntry::NIL_VAL,
                    (|e| e.is_prefix()) as fn(OrderedEntry) -> bool,
                );
                let buf_ptr =
                    &buf as *const RaceBuffer<'_, OrderedEntry, fn(OrderedEntry) -> bool> as usize;
                ptr_s.send(buf_ptr).unwrap();

                let mut last_prefix = false;
                for i in 1..=NUM_ENTRIES {
                    if last_prefix {
                        buf.write(OrderedEntry::from_index_suffix(i));
                        last_prefix = false;
                    } else {
                        if random() && random() {
                            buf.write(OrderedEntry::from_index_prefix(i));
                            last_prefix = true;
                        } else {
                            buf.write(OrderedEntry::from_index(i));
                        }
                    }

                    let mut sleep_time: u64 = random();
                    sleep_time = sleep_time % 1000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                barr_r.wait();
            });
            s.spawn(move |_| {
                let buf_ptr = ptr_r.recv().unwrap()
                    as *const RaceBuffer<'_, OrderedEntry, fn(OrderedEntry) -> bool>;
                let mut rbuf = Vec::new();
                let mut reader = RaceBufferReader::new(
                    STORAGE_LEN,
                    || unsafe { buf_ptr.as_ref().unwrap().read_wcurs() },
                    |i| unsafe { buf_ptr.as_ref().unwrap().read_storage(i) },
                    |e| e.is_prefix(),
                    OrderedEntry::NIL_VAL,
                );

                while rbuf.len() < NUM_ENTRIES as usize {
                    reader.read(&mut rbuf);
                    let mut sleep_time: u64 = random();
                    sleep_time = sleep_time % 3000;
                    std::thread::sleep(Duration::from_nanos(sleep_time));
                }
                thread::sleep(Duration::from_millis(100));
                reader.read(&mut rbuf);
                assert_eq!(rbuf.len(), NUM_ENTRIES as usize);
                assert!(OrderedEntry::entries_correct_index(&rbuf[..]));
                assert!(OrderedEntry::double_entries_consistent(&rbuf[..]));
                barr_w.wait();
            });
        })
        .unwrap();
    }
}
