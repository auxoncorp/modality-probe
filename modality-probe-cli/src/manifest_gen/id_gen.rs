use crate::{error::GracefulExit, exit_error};
use core::num::NonZeroU32;
use sha3::{Digest, Sha3_256};
use std::convert::TryInto;
use std::hash::Hash;
use std::str::FromStr;
use uuid::Uuid;

/// Inclusive non-zero ID (u32) range
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct NonZeroIdRange {
    inclusive_start: NonZeroU32,
    inclusive_end: NonZeroU32,
}

impl NonZeroIdRange {
    pub fn new(inclusive_start: NonZeroU32, inclusive_end: NonZeroU32) -> Option<Self> {
        if inclusive_start.get() > inclusive_end.get() {
            None
        } else {
            Some(NonZeroIdRange {
                inclusive_start,
                inclusive_end,
            })
        }
    }

    pub fn contains(&self, value: NonZeroU32) -> bool {
        value.get() >= self.inclusive_start.get() && value.get() <= self.inclusive_end.get()
    }
}

#[derive(Debug)]
pub struct IdGen {
    id_range: NonZeroIdRange,
    uuid: Uuid,
}

impl IdGen {
    pub fn new(id_range: NonZeroIdRange) -> Self {
        IdGen {
            id_range,
            uuid: Uuid::new_v4(),
        }
    }

    pub fn regenerate_uuid(&mut self) {
        self.uuid = Uuid::new_v4();
    }

    pub fn hashed_id(&mut self, token: &str) -> NonZeroU32 {
        let mut max_tries = std::u16::MAX;
        loop {
            let hash = self.token_hash(token);
            if let Some(non_zero_hash) = NonZeroU32::new(hash) {
                if self.id_range.contains(non_zero_hash) {
                    return non_zero_hash;
                }
            }

            self.regenerate_uuid();

            // Escape hatch
            max_tries = max_tries.saturating_sub(1);
            if max_tries == 0 {
                exit_error!("manifest-gen", "Exceeded the id-hashing retry limit");
            }
        }
    }

    fn token_hash(&self, token: &str) -> u32 {
        let mut hasher = Sha3_256::new();
        hasher.update(self.uuid.as_bytes());
        hasher.update(token.as_bytes());
        let hash = hasher.finalize();
        let bytes: &[u8; 32] = hash.as_ref();
        let be16_bytes = u16::from_be_bytes(
            bytes[0..2]
                .try_into()
                .unwrap_or_exit("Can't make a u16 from bytes"),
        );
        let be32_bytes = u32::from_be_bytes(
            bytes[0..4]
                .try_into()
                .unwrap_or_exit("Can't make a u32 from bytes"),
        );
        let id = u32::from(be16_bytes)
            .overflowing_mul(0xFFFF_FFFF)
            .0
            .overflowing_add(be32_bytes)
            .0;
        id % self.id_range.inclusive_end.get()
    }
}

impl FromStr for NonZeroIdRange {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = s.trim().split("..").collect();

        if parts.len() != 2 {
            Err("Can't split the input into components")
        } else {
            let start = parts[0]
                .parse::<u32>()
                .map_err(|_| "Can't parse start component as u32")?;

            let end = if parts[1].starts_with('=') {
                parts[1]
                    .trim_start_matches('=')
                    .parse::<u32>()
                    .map_err(|_| "Can't parse end component as u32")?
            } else {
                let excl_end = parts[1]
                    .parse::<u32>()
                    .map_err(|_| "Can't parse end component as u32")?;
                excl_end.saturating_sub(1)
            };

            if start > end {
                return Err("Range start cannot exceed the end");
            }

            let inclusive_start = NonZeroU32::new(start).ok_or("Range start must be non-zero")?;
            let inclusive_end = NonZeroU32::new(end).ok_or("Range end must be non-zero")?;

            Ok(NonZeroIdRange {
                inclusive_start,
                inclusive_end,
            })
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        fn gen_non_zero_id()(raw_id in 1..=std::u32::MAX) -> NonZeroU32 {
            NonZeroU32::new(raw_id).unwrap()
        }
    }

    #[test]
    fn id_range_from_str() {
        assert_eq!(
            NonZeroIdRange::from_str("1..=10"),
            Ok(NonZeroIdRange {
                inclusive_start: NonZeroU32::new(1).unwrap(),
                inclusive_end: NonZeroU32::new(10).unwrap(),
            })
        );

        assert_eq!(
            NonZeroIdRange::from_str("10..100"),
            Ok(NonZeroIdRange {
                inclusive_start: NonZeroU32::new(10).unwrap(),
                inclusive_end: NonZeroU32::new(99).unwrap(),
            })
        );
    }

    #[test]
    fn id_range_from_str_errors() {
        assert!(NonZeroIdRange::from_str("0..10").is_err());
        assert!(NonZeroIdRange::from_str("1..0").is_err());
        assert!(NonZeroIdRange::from_str("0..=0").is_err());
        assert!(NonZeroIdRange::from_str("10..=1").is_err());
        assert!(NonZeroIdRange::from_str("1..1").is_err());
    }

    #[test]
    fn basic_id_range_contains() {
        let r =
            NonZeroIdRange::new(NonZeroU32::new(2).unwrap(), NonZeroU32::new(10).unwrap()).unwrap();
        assert!(!r.contains(NonZeroU32::new(1).unwrap()));
        assert!(r.contains(NonZeroU32::new(2).unwrap()));
        assert!(r.contains(NonZeroU32::new(10).unwrap()));
        assert!(!r.contains(NonZeroU32::new(11).unwrap()));
    }

    proptest! {
        #[test]
        fn id_range_contains(a in gen_non_zero_id(), b in gen_non_zero_id()) {
            let (inc_start, inc_end)  = if a.get() <= b.get() {
                (a, b)
            } else {
                (b,a )
            };

            let r = NonZeroIdRange::new(inc_start, inc_end).unwrap();
            assert!(r.contains(inc_start));
            assert!(r.contains(inc_end));
        }
    }

    proptest! {
        #[test]
        fn id_hashing_in_range(a in gen_non_zero_id(), b in gen_non_zero_id()) {
            let r = if a.get() <= b.get() {
                NonZeroIdRange::new(a, b).unwrap()
            } else {
                NonZeroIdRange::new(b, a).unwrap()
            };

            let mut gen = IdGen::new(r);
            let id = gen.hashed_id("MY_PROBE_ID");
            assert!(r.contains(id));
        }
    }
}
