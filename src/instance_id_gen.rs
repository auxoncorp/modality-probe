use crate::id::InstanceId;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering::SeqCst;
use static_assertions::{assert_eq_align, assert_eq_size, const_assert};

assert_eq_size!(usize, InstanceIdGen);
assert_eq_align!(usize, InstanceIdGen);
const_assert!((InstanceId::MAX_ID as usize) < core::usize::MAX);

/// Thread-safe InstanceId generator, values start at zero and stop at InstanceId::MAX_ID
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct InstanceIdGen(AtomicUsize);

impl InstanceIdGen {
    const MAX_ID: usize = InstanceId::MAX_ID as usize;

    /// Create a new InstanceIdGen, the generated values start at zero and stop at InstanceId::MAX_ID
    pub const fn new() -> Self {
        InstanceIdGen(AtomicUsize::new(0))
    }

    /// Get the next available InstanceId, returns None if the id range has been exhausted
    pub fn next(&self) -> Option<InstanceId> {
        let id = self.0.fetch_update(SeqCst, SeqCst, |current_value| {
            if current_value <= Self::MAX_ID {
                Some(current_value + 1)
            } else {
                None
            }
        });
        id.ok().map(|id| InstanceId::new(id as _)).flatten()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generates_full_range() {
        let gen = InstanceIdGen::new();
        for i in 0..=core::u8::MAX {
            if i <= InstanceId::MAX_ID {
                assert_eq!(i, u8::from(gen.next().unwrap()));
            } else {
                assert_eq!(None, gen.next());
            }
        }
        for _ in 0..=core::u8::MAX {
            assert_eq!(None, gen.next());
        }
        assert_eq!((InstanceId::MAX_ID as usize) + 1, gen.0.load(SeqCst));
    }
}
