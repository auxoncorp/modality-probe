//! Wall clock time
//!
//! Time is fixed to nanosecond precision, with user supplied resolution.

/// 61 bit nanosecond wall clock time
///
/// Note that the upper 3 bits are reserved for internal use.
///
/// This can represent approximately 73 years.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[cfg_attr(
feature = "std",
derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct Nanoseconds(u64);

/// Nanosecond time resolution
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[cfg_attr(
feature = "std",
derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct NanosecondResolution(pub u32);

/// Nanosecond high bits
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
#[cfg_attr(
feature = "std",
derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct NanosecondsHighBits(pub [u8; 4]);

/// Nanosecond low bits
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
#[cfg_attr(
feature = "std",
derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct NanosecondsLowBits(pub [u8; 4]);

/// Wall clock identifier, indicates the time domain
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[cfg_attr(
feature = "std",
derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct WallClockId(pub u16);

impl Nanoseconds {
    /// The largest permissible backing time value
    pub const MAX: Self = Nanoseconds(
        0b0001_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111,
    );

    /// Zero value time
    pub const ZERO: Self = Nanoseconds(0);

    /// One seconds worth of nanoseconds
    pub const SECOND: Self = Nanoseconds(1_000_000_000);
    /// One milliseconds worth of nanoseconds
    pub const MILLISECOND: Self = Nanoseconds(1_000_000);
    /// One microseconds worth of nanoseconds
    pub const MICROSECOND: Self = Nanoseconds(1_000);

    /// Create a zero value time
    pub const fn zero() -> Self {
        Nanoseconds(0)
    }

    /// Time must not be greater than Nanoseconds::MAX
    pub const fn new(t: u64) -> Option<Self> {
        if t > Self::MAX.0 {
            None
        } else {
            Some(Nanoseconds(t))
        }
    }

    /// Mask off bits 61..=63
    pub const fn new_truncate(t: u64) -> Self {
        Nanoseconds(t & Self::MAX.0)
    }

    /// Create time from little endian parts.
    ///
    /// Time must not be greater than Nanoseconds::MAX
    pub const fn from_parts(
        low_bits: NanosecondsLowBits,
        high_bits: NanosecondsHighBits,
    ) -> Option<Self> {
        let t = Self::combine_parts(low_bits, high_bits);
        Self::new(t)
    }

    /// Mask off bits 61..=63
    pub const fn from_parts_truncate(
        low_bits: NanosecondsLowBits,
        high_bits: NanosecondsHighBits,
    ) -> Self {
        let t = Self::combine_parts(low_bits, high_bits);
        Self::new_truncate(t)
    }

    const fn combine_parts(low_bits: NanosecondsLowBits, high_bits: NanosecondsHighBits) -> u64 {
        let low = low_bits.0;
        let high = high_bits.0;
        u64::from_le_bytes([
            low[0], low[1], low[2], low[3], high[0], high[1], high[2], high[3],
        ])
    }

    /// Get the underlying value as a convenient primitive
    pub const fn get(&self) -> u64 {
        self.0
    }

    /// Split time into little endian parts.
    pub fn split(self) -> (NanosecondsLowBits, NanosecondsHighBits) {
        let le_bytes = self.0.to_le_bytes();
        let low_bits = NanosecondsLowBits([le_bytes[0], le_bytes[1], le_bytes[2], le_bytes[3]]);
        let high_bits = NanosecondsHighBits([le_bytes[4], le_bytes[5], le_bytes[6], le_bytes[7]]);
        (low_bits, high_bits)
    }

    /// Get the underlying value as a convenient primitive converted to seconds
    pub fn as_secs(&self) -> u64 {
        self.0 / Self::SECOND.0
    }

    /// Get the underlying value as a convenient primitive converted to milliseconds
    pub fn as_millis(&self) -> u64 {
        self.0 / Self::MILLISECOND.0
    }

    /// Get the underlying value as a convenient primitive converted to microseconds
    pub fn as_micros(&self) -> u64 {
        self.0 / Self::MICROSECOND.0
    }
}

impl Default for Nanoseconds {
    fn default() -> Self {
        Nanoseconds::zero()
    }
}

impl NanosecondResolution {
    /// Unspecified resolution
    pub const UNSPECIFIED: Self = NanosecondResolution(0);

    /// Returns true if the resolution is unspecified
    pub fn is_unspecified(&self) -> bool {
        self.0 == Self::UNSPECIFIED.0
    }
}

impl Default for NanosecondResolution {
    fn default() -> Self {
        NanosecondResolution::UNSPECIFIED
    }
}

impl From<u32> for NanosecondResolution {
    fn from(r: u32) -> Self {
        NanosecondResolution(r)
    }
}

impl From<NanosecondResolution> for u32 {
    fn from(r: NanosecondResolution) -> Self {
        r.0
    }
}

impl From<[u8; 4]> for NanosecondsHighBits {
    fn from(bits: [u8; 4]) -> Self {
        NanosecondsHighBits(bits)
    }
}

impl From<NanosecondsHighBits> for [u8; 4] {
    fn from(bits: NanosecondsHighBits) -> Self {
        bits.0
    }
}

impl From<[u8; 4]> for NanosecondsLowBits {
    fn from(bits: [u8; 4]) -> Self {
        NanosecondsLowBits(bits)
    }
}

impl From<NanosecondsLowBits> for [u8; 4] {
    fn from(bits: NanosecondsLowBits) -> Self {
        bits.0
    }
}

impl WallClockId {
    /// This time domain is local to the probe only
    pub const LOCAL_ONLY: Self = WallClockId(0);

    /// This time domain is local to the probe only
    pub const fn local_only() -> Self {
        WallClockId(0)
    }

    /// Returns true if this wall clock id is local to the probe only
    pub fn is_local_only(&self) -> bool {
        *self == Self::LOCAL_ONLY
    }
}

impl Default for WallClockId {
    fn default() -> Self {
        WallClockId::local_only()
    }
}

impl From<u16> for WallClockId {
    fn from(bits: u16) -> Self {
        WallClockId(bits)
    }
}

impl From<WallClockId> for u16 {
    fn from(bits: WallClockId) -> Self {
        bits.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn const_helpers() {
        assert_ne!(Nanoseconds::MAX.get(), 0);
        assert_eq!(Nanoseconds::zero().get(), 0);
        assert_eq!(Nanoseconds::MICROSECOND.get(), 1_000);
        assert_eq!(
            Nanoseconds::MILLISECOND.get(),
            1_000 * Nanoseconds::MICROSECOND.get()
        );
        assert_eq!(
            Nanoseconds::SECOND.get(),
            1_000 * Nanoseconds::MILLISECOND.get()
        );
    }

    #[test]
    fn invalid() {
        assert_eq!(Nanoseconds::new(core::u64::MAX), None);
        assert_eq!(Nanoseconds::new(core::u64::MAX >> 1), None);
        assert_eq!(Nanoseconds::new(core::u64::MAX >> 2), None);

        let low_bits = NanosecondsLowBits(core::u32::MAX.to_le_bytes());
        let high_bits = NanosecondsHighBits(core::u32::MAX.to_le_bytes());
        assert_eq!(None, Nanoseconds::from_parts(low_bits, high_bits));
    }

    #[test]
    fn truncation() {
        assert_eq!(Nanoseconds::MAX, Nanoseconds::new_truncate(core::u64::MAX));

        let low_bits = NanosecondsLowBits(core::u32::MAX.to_le_bytes());
        let high_bits = NanosecondsHighBits(core::u32::MAX.to_le_bytes());
        assert_eq!(
            Nanoseconds::MAX,
            Nanoseconds::from_parts_truncate(low_bits, high_bits)
        );
    }

    proptest! {
        #[test]
        fn round_trip_time(raw_time_in in 0_u64..=Nanoseconds::MAX.0) {
            let t = Nanoseconds::new(raw_time_in).unwrap();
            prop_assert_eq!(t.get(), raw_time_in);
            let (low_bits, high_bits) = t.split();
            prop_assert_eq!(u32::from_le_bytes(low_bits.0), (raw_time_in & core::u32::MAX as u64) as u32);
            prop_assert_eq!(
                u32::from_le_bytes(high_bits.0),
                (raw_time_in >> 32 & core::u32::MAX as u64) as u32
            );
            let t_out = Nanoseconds::from_parts(low_bits, high_bits).unwrap();
            prop_assert_eq!(t, t_out);
            prop_assert_eq!(raw_time_in, t_out.get());
        }
    }
}
