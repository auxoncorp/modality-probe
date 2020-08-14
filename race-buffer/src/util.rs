use super::*;
use std::fmt;
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
}

#[derive(Copy, Clone)]
pub(crate) enum OutputOrderedEntry {
    Present(WholeEntry<OrderedEntry>),
    Missed(u64),
}

impl OutputOrderedEntry {
    // Invariant: Check if entries all have correct index
    pub(crate) fn check_entries_correct_index(rbuf: &[OutputOrderedEntry]) {
        let mut current_index = 0;
        for output_entry in rbuf {
            match output_entry {
                OutputOrderedEntry::Missed(n) => current_index += n,
                OutputOrderedEntry::Present(entry) => match entry {
                    WholeEntry::Single(single) => {
                        assert_eq!(single.to_index() as u64, current_index);
                        current_index += 1;
                    }
                    WholeEntry::Double(first, second) => {
                        assert_eq!(first.to_index() as u64, current_index);
                        assert_eq!(second.to_index() as u64, current_index + 1);
                        current_index += 2;
                    }
                },
            }
        }
    }

    // Invariant: Check if entries all have correct index
    pub(crate) fn check_double_entries_consistent(rbuf: &[OutputOrderedEntry]) {
        for output_entry in rbuf {
            if let OutputOrderedEntry::Present(WholeEntry::Single(entry)) = output_entry {
                assert!(!entry.is_suffix() && !entry.is_prefix())
            } else if let OutputOrderedEntry::Present(WholeEntry::Double(first, second)) =
                output_entry
            {
                assert!(first.is_prefix());
                assert!(second.is_suffix());
            }
        }
    }
}

pub(crate) struct RawPtrSnapper<'a>(*const RaceBuffer<'a, OrderedEntry>);

impl<'a> RawPtrSnapper<'a> {
    pub(crate) fn new(ptr: *const RaceBuffer<'a, OrderedEntry>) -> RawPtrSnapper<'a> {
        RawPtrSnapper(ptr)
    }
}

#[derive(Debug)]
pub(crate) struct RawPtrSnapperError;

impl fmt::Display for RawPtrSnapperError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error snapping using raw pointer")
    }
}

impl std::error::Error for RawPtrSnapperError {}

impl async_reader::Snapper<OrderedEntry> for RawPtrSnapper<'_> {
    type Error = RawPtrSnapperError;

    fn snap_write_seqn_high(&self) -> Result<u32, RawPtrSnapperError> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_write_seqn().high) }
    }

    fn snap_write_seqn_low(&self) -> Result<u32, RawPtrSnapperError> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_write_seqn().low) }
    }

    fn snap_overwrite_seqn_high(&self) -> Result<u32, RawPtrSnapperError> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_overwrite_seqn().high) }
    }

    fn snap_overwrite_seqn_low(&self) -> Result<u32, RawPtrSnapperError> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().get_overwrite_seqn().low) }
    }

    fn snap_storage(&self, index: usize) -> Result<OrderedEntry, RawPtrSnapperError> {
        // Ensure reads are not reordered
        fence(Ordering::Acquire);
        unsafe { Ok(self.0.as_ref().unwrap().read_storage((index as u64).into())) }
    }
}
