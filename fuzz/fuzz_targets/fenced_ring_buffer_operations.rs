#![no_main]
use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

use core::mem::MaybeUninit;
use fenced_ring_buffer::{Entry, FencedRingBuffer};

#[derive(Arbitrary, Debug)]
struct Script {
    buffer_size: u8,
    use_base_2_indexing: bool,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Push(NumEntry),
    PushDouble(NumEntry, NumEntry),
    NumMissed,
    Peek,
    Pop,
    Iter,
    Drain,
    GetLinearSlices,
    Len,
    IsEmpty,
    IsFull,
    Capacity,
    GetSlice,
}

#[derive(Arbitrary, Debug, Copy, Clone, Eq, PartialEq)]
struct NumEntry(u32);

impl Entry for NumEntry {
    /// Return true if entry is the first in a double entry
    fn is_prefix(&self) -> bool {
        self.0 & 0b10000000_00000000_00000000_00000000 != 0
    }
}

fn run(s: Script) {
    let mut bytes = vec![MaybeUninit::<u8>::uninit(); s.buffer_size as usize];
    let mut frb = match FencedRingBuffer::<NumEntry>::new_from_uninit_bytes(
        &mut bytes[..],
        s.use_base_2_indexing,
    ) {
        Ok(x) => x,
        Err(_) => return,
    };

    for op in s.ops.into_iter() {
        match op {
            Op::Push(x) => {
                let _ = frb.safe_push(x);
            }
            Op::PushDouble(x, y) => {
                let _ = frb.safe_push_double(x, y);
            }
            Op::NumMissed => {
                let _ = frb.num_missed();
            }
            Op::Peek => {
                let _ = frb.peek();
            }
            Op::Pop => {
                let _ = frb.pop();
            }
            Op::Iter => for _ in frb.iter() {},
            Op::Drain => for _ in frb.drain() {},
            Op::GetLinearSlices => {
                // maybe try to use them?
                let _ = frb.get_linear_slices();
            }
            Op::Len => {
                let _ = frb.len();
            }
            Op::IsEmpty => {
                let _ = frb.is_empty();
            }
            Op::IsFull => {
                let _ = frb.is_full();
            }
            Op::Capacity => {
                let _ = frb.capacity();
            }
            Op::GetSlice => {
                // maybe try to use it?
                let _ = frb.get_slice();
            }
        }
    }
}

fuzz_target!(|s: Script| {
    run(s);
});
