use super::*;
use std::error::Error;
use std::sync::atomic::{fence, Ordering};

#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(transparent)]
pub(crate) struct OrderedEntry(u32);

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
    pub(crate) fn entries_correct_index(rbuf: &[PossiblyMissed<OrderedEntry>]) -> bool {
        for (idx, entry) in rbuf
            .iter()
            .enumerate()
            .filter(|(_, e)| **e != PossiblyMissed::Missed)
        {
            if entry.assume_not_missed().to_index() != idx as u32 {
                return false;
            }
        }
        return true;
    }

    // Invariant: Check if entries all have correct index
    pub(crate) fn double_entries_consistent(rbuf: &[PossiblyMissed<OrderedEntry>]) -> bool {
        if rbuf.len() == 0 {
            return true;
        }
        if let PossiblyMissed::Entry(first_entry) = rbuf[0] {
            if first_entry.is_suffix() {
                return false;
            }
        }
        if let PossiblyMissed::Entry(last_entry) = rbuf.last().unwrap() {
            if last_entry.is_prefix_unchecked() {
                return false;
            }
        }
        for i in 0..(rbuf.len() - 1) {
            match rbuf[i] {
                PossiblyMissed::Missed => {
                    if let PossiblyMissed::Entry(next) = rbuf[i + 1] {
                        if next.is_suffix() {
                            return false;
                        }
                    }
                }
                PossiblyMissed::Entry(current) => {
                    if current.is_prefix_unchecked() {
                        if let PossiblyMissed::Entry(next) = rbuf[i + 1] {
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

pub(crate) struct RawPtrSnapper<'a>(*const writer::RaceBuffer<'a, OrderedEntry>);

impl<'a> RawPtrSnapper<'a> {
    pub(crate) fn new(ptr: *const writer::RaceBuffer<'a, OrderedEntry>) -> RawPtrSnapper<'a> {
        RawPtrSnapper(ptr)
    }
}

impl reader::Snapper<OrderedEntry> for RawPtrSnapper<'_> {
    fn snap_write_seqn(&self) -> Result<u32, Box<dyn Error>> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_write_seqn()) }
    }

    fn snap_overwrite_seqn(&self) -> Result<u32, Box<dyn Error>> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_overwrite_seqn()) }
    }

    fn snap_storage(&self, index: u32) -> Result<OrderedEntry, Box<dyn Error>> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().read_storage(index)) }
    }
}
