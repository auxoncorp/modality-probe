//! Wire protocols

use crate::{MergeError, ProduceError};

pub mod bulk_report;
pub mod causal_snapshot;
pub mod chunked_report;
pub mod report;

pub use bulk_report::*;
pub use causal_snapshot::*;
pub use chunked_report::*;

impl From<MissingBytes> for ProduceError {
    #[inline]
    fn from(_: MissingBytes) -> Self {
        ProduceError::InsufficientDestinationSize
    }
}

impl From<MissingBytes> for MergeError {
    #[inline]
    fn from(_: MissingBytes) -> Self {
        MergeError::InsufficientSourceSize
    }
}

impl From<InvalidWireProbeId> for MergeError {
    #[inline]
    fn from(_: InvalidWireProbeId) -> Self {
        MergeError::ExternalHistorySemantics
    }
}

impl From<CausalSnapshotWireError> for MergeError {
    #[inline]
    fn from(e: CausalSnapshotWireError) -> Self {
        match e {
            CausalSnapshotWireError::MissingBytes => MergeError::InsufficientSourceSize,
            CausalSnapshotWireError::InvalidProbeId(_) => MergeError::ExternalHistorySemantics,
        }
    }
}

mod le_bytes {
    // This pattern is mostly copied from
    // https://github.com/BurntSushi/byteorder.
    // We can't use that crate due to rust-lang/cargo#5730.
    macro_rules! read_bytes {
        ($ty:ty, $size:expr, $src:expr) => {{
            use core::ptr::copy_nonoverlapping;
            debug_assert!($size == ::core::mem::size_of::<$ty>());
            debug_assert!($size <= $src.len());
            let mut data: $ty = 0;
            unsafe {
                copy_nonoverlapping($src.as_ptr(), &mut data as *mut $ty as *mut u8, $size);
            }
            data.to_le()
        }};
    }

    // This pattern is mostly copied from
    // https://github.com/BurntSushi/byteorder
    // We can't use that crate due to rust-lang/cargo#5730.
    macro_rules! write_bytes {
        ($ty:ty, $size:expr, $n:expr, $dst:expr) => {{
            use core::ptr::copy_nonoverlapping;
            debug_assert!($size <= $dst.len());
            unsafe {
                let bytes = *(&$n.to_le() as *const _ as *const [u8; $size]);
                copy_nonoverlapping((&bytes).as_ptr(), $dst.as_mut_ptr(), $size);
            }
        }};
    }

    /// Reads a u16 from `bytes`.
    ///
    /// # Panics
    ///
    /// Panics when `bytes.len() < 2`.
    #[inline]
    pub fn read_u16(bytes: &[u8]) -> u16 {
        read_bytes!(u16, 2, bytes)
    }

    /// Reads a u16 from `bytes`.
    ///
    /// # Panics
    ///
    /// Panics when `bytes.len() < 4`.
    #[inline]
    pub fn read_u32(bytes: &[u8]) -> u32 {
        read_bytes!(u32, 4, bytes)
    }

    /// Writes a u16 `value` to `bytes`.
    ///
    /// # Panics
    ///
    /// Panics when `bytes.len() < 2`.
    #[inline]
    pub fn write_u16(bytes: &mut [u8], value: u16) {
        write_bytes!(u16, 2, value, bytes);
    }

    /// Writes a u32 `value` to `bytes`.
    ///
    /// # Panics
    ///
    /// Panics when `bytes.len() < 4`.
    #[inline]
    pub fn write_u32(bytes: &mut [u8], value: u32) {
        write_bytes!(u32, 4, value, bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn le_u16(
            b0 in proptest::num::u8::ANY,
            b1 in proptest::num::u8::ANY,
        ) {
            let expected_value = u16::from_le_bytes([b0, b1]);
            let rbytes = [b0, b1];
            let value = le_bytes::read_u16(&rbytes[0..2]);
            assert_eq!(value, expected_value);
            let mut wbytes = [!b0, !b1];
            le_bytes::write_u16(&mut wbytes[0..2], expected_value);
            assert_eq!(rbytes, wbytes);
        }
    }

    proptest! {
        #[test]
        fn le_u32(
            b0 in proptest::num::u8::ANY,
            b1 in proptest::num::u8::ANY,
            b2 in proptest::num::u8::ANY,
            b3 in proptest::num::u8::ANY,
        ) {
            let expected_value = u32::from_le_bytes([b0, b1, b2, b3]);
            let rbytes = [b0, b1, b2, b3];
            let value = le_bytes::read_u32(&rbytes[0..4]);
            assert_eq!(value, expected_value);
            let mut wbytes = [!b0, !b1, !b2, !b3];
            le_bytes::write_u32(&mut wbytes[0..4], expected_value);
            assert_eq!(rbytes, wbytes);
        }
    }
}
