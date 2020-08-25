//! A wire protocol for representing Modality probe causal snaphots

use crate::{wire::le_bytes, ProbeEpoch, ProbeId, ProbeTicks, CausalSnapshot, LogicalClock, InvalidProbeId};
use core::mem::size_of;
use static_assertions::const_assert_eq;
use core::convert::TryFrom;

/// Everything that can go wrong when attempting to interpret a causal snaphot
/// to/from the wire representation
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum CausalSnapshotWireError {
    /// There weren't enough bytes for a full causal snapshot
    MissingBytes,
    /// The probe id didn't follow the rules for being
    /// a valid Modality probe-specifying ProbeId
    InvalidProbeId(u32),
}

/// Error that indicates there weren't enough bytes for a full causal snapshot
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct MissingBytes;

/// Error that indicates the probe id didn't follow the rules for being
/// a valid Modality probe-specifying ProbeId
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct InvalidWireProbeId(u32);

impl From<MissingBytes> for CausalSnapshotWireError {
    fn from(_: MissingBytes) -> Self {
        CausalSnapshotWireError::MissingBytes
    }
}

impl From<InvalidWireProbeId> for CausalSnapshotWireError {
    fn from(e: InvalidWireProbeId) -> Self {
        CausalSnapshotWireError::InvalidProbeId(e.0)
    }
}

/// A read/write wrapper around a causal snaphot buffer
#[derive(Debug, Clone)]
pub struct WireCausalSnapshot<T: AsRef<[u8]>> {
    buffer: T,
}

const_assert_eq!(size_of::<crate::CausalSnapshot>(), field::REST.start);

mod field {
    type Field = ::core::ops::Range<usize>;
    type Rest = ::core::ops::RangeFrom<usize>;

    /// LogicalClock.id
    pub const PROBE_ID: Field = 0..4;

    /// LogicalClock.clock
    pub const TICKS: Field = 4..6;

    /// LogicalClock.epoch
    pub const EPOCH: Field = 6..8;

    /// Reserved field
    pub const RESERVED_0: Field = 8..10;

    /// Reserved field
    pub const RESERVED_1: Field = 10..12;

    /// Remaining bytes
    pub const REST: Rest = 12..;
}

impl<T: AsRef<[u8]>> WireCausalSnapshot<T> {
    /// Construct a causal snaphot from a byte buffer
    pub fn new_unchecked(buffer: T) -> WireCausalSnapshot<T> {
        WireCausalSnapshot { buffer }
    }

    /// Construct a causal snaphot from a byte buffer, with checks.
    ///
    /// A combination of:
    /// * [new_unchecked](struct.CausalSnapshot.html#method.new_unchecked)
    /// * [check_len](struct.CausalSnapshot.html#method.check_len)
    pub fn new(buffer: T) -> Result<WireCausalSnapshot<T>, MissingBytes> {
        let r = Self::new_unchecked(buffer);
        r.check_len()?;
        Ok(r)
    }

    /// Ensure that no accessor method will panic if called.
    ///
    /// Returns `Err(CausalSnapshotWireError::MissingBytes)` if the buffer
    /// is too short.
    pub fn check_len(&self) -> Result<(), MissingBytes> {
        let len = self.buffer.as_ref().len();
        if len < field::REST.start {
            Err(MissingBytes)
        } else {
            Ok(())
        }
    }

    /// Consumes the causal snaphot, returning the underlying buffer
    pub fn into_inner(self) -> T {
        self.buffer
    }

    /// Return the length of a buffer required to hold a causal snaphot
    pub fn min_buffer_len() -> usize {
        field::REST.start
    }

    /// Return the `probe_id` field
    #[inline]
    pub fn probe_id(&self) -> Result<ProbeId, InvalidWireProbeId> {
        let data = self.buffer.as_ref();
        let raw_probe_id = le_bytes::read_u32(&data[field::PROBE_ID]);
        match ProbeId::new(raw_probe_id) {
            Some(id) => Ok(id),
            None => Err(InvalidWireProbeId(raw_probe_id)),
        }
    }

    /// Return the `epoch` field
    #[inline]
    pub fn epoch(&self) -> ProbeEpoch {
        let data = self.buffer.as_ref();
        ProbeEpoch(le_bytes::read_u16(&data[field::EPOCH]))
    }

    /// Return the `ticks` field
    #[inline]
    pub fn ticks(&self) -> ProbeTicks {
        let data = self.buffer.as_ref();
        ProbeTicks(le_bytes::read_u16(&data[field::TICKS]))
    }

    /// Return the `reserved_0` field
    #[inline]
    pub fn reserved_0(&self) -> [u8; 2] {
        let data = self.buffer.as_ref();
        let field = &data[field::RESERVED_0];
        [field[0], field[1]]
    }

    /// Return the `reserved_1` field
    #[inline]
    pub fn reserved_1(&self) -> [u8; 2] {
        let data = self.buffer.as_ref();
        let field = &data[field::RESERVED_1];
        [field[0], field[1]]
    }
}

impl<T: AsRef<[u8]> + AsMut<[u8]>> WireCausalSnapshot<T> {
    /// Set the `probe_id` field
    #[inline]
    pub fn set_probe_id(&mut self, value: ProbeId) {
        let data = self.buffer.as_mut();
        le_bytes::write_u32(&mut data[field::PROBE_ID], value.get_raw());
    }

    /// Set the `epoch` field
    #[inline]
    pub fn set_epoch(&mut self, value: ProbeEpoch) {
        let data = self.buffer.as_mut();
        le_bytes::write_u16(&mut data[field::EPOCH], value.0);
    }

    /// Set the `clock` field
    #[inline]
    pub fn set_ticks(&mut self, value: ProbeTicks) {
        let data = self.buffer.as_mut();
        le_bytes::write_u16(&mut data[field::TICKS], value.0);
    }

    /// Set the `reserved_0` field
    #[inline]
    pub fn set_reserved_0(&mut self, value: [u8; 2]) {
        let data = self.buffer.as_mut();
        data[field::RESERVED_0][0] = value[0];
        data[field::RESERVED_0][1] = value[1];
    }

    /// Set the `reserved_1` field
    #[inline]
    pub fn set_reserved_1(&mut self, value: [u8; 2]) {
        let data = self.buffer.as_mut();
        data[field::RESERVED_1][0] = value[0];
        data[field::RESERVED_1][1] = value[1];
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for WireCausalSnapshot<T> {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl CausalSnapshot {
    /// Construct a causal snapshot from a sequence of little endian bytes
    pub fn from_le_bytes(bytes: [u8; 12]) -> Result<Self, InvalidProbeId> {
        let snapshot = WireCausalSnapshot::new_unchecked(bytes);
        Ok(CausalSnapshot {
            clock: LogicalClock {
                id: snapshot.probe_id().map_err(|_| InvalidProbeId)?,
                epoch: snapshot.epoch(),
                ticks: snapshot.ticks(),
            },
            reserved_0: snapshot.reserved_0(),
            reserved_1: snapshot.reserved_1(),
        })
    }

    /// Return a causal snapshot as a sequence of little endian bytes
    pub fn to_le_bytes(&self) -> [u8; 12] {
        let mut arr = [0u8; 12];
        self.write_into_le_bytes_exact(&mut arr);
        arr
    }

    /// Writes a causal snapshot into an array of little endian bytes.
    /// Always writes exactly 12 bytes, the full length of the provided array.
    pub fn write_into_le_bytes_exact(&self, bytes: &mut [u8; 12]) {
        let mut wire = WireCausalSnapshot::new_unchecked(bytes);
        wire.set_probe_id(self.clock.id);
        wire.set_epoch(self.clock.epoch);
        wire.set_ticks(self.clock.ticks);
        wire.set_reserved_0(self.reserved_0);
        wire.set_reserved_1(self.reserved_1);
    }

    /// Writes a causal snapshot into a slice of little endian bytes.
    ///
    /// Returns the number of bytes written, which should always be 12.
    pub fn write_into_le_bytes(&self, bytes: &mut [u8]) -> Result<usize, MissingBytes> {
        let mut wire = WireCausalSnapshot::new_unchecked(bytes);
        wire.check_len()?;
        wire.set_probe_id(self.clock.id);
        wire.set_ticks(self.clock.ticks);
        wire.set_epoch(self.clock.epoch);
        wire.set_reserved_0(self.reserved_0);
        wire.set_reserved_1(self.reserved_1);
        Ok(WireCausalSnapshot::<&[u8]>::min_buffer_len())
    }
}

impl TryFrom<&[u8]> for CausalSnapshot {
    type Error = CausalSnapshotWireError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let snapshot = WireCausalSnapshot::new(bytes)?;
        Ok(CausalSnapshot {
            clock: LogicalClock {
                id: snapshot.probe_id()?,
                epoch: snapshot.epoch(),
                ticks: snapshot.ticks(),
            },
            reserved_0: snapshot.reserved_0(),
            reserved_1: snapshot.reserved_1(),
        })
    }
}

impl TryFrom<&[u8; 12]> for CausalSnapshot {
    type Error = InvalidProbeId;

    fn try_from(bytes: &[u8; 12]) -> Result<Self, Self::Error> {
        let snapshot = WireCausalSnapshot::new_unchecked(bytes);
        Ok(CausalSnapshot {
            clock: LogicalClock {
                id: snapshot.probe_id().map_err(|_| InvalidProbeId)?,
                epoch: snapshot.epoch(),
                ticks: snapshot.ticks(),
            },
            reserved_0: snapshot.reserved_0(),
            reserved_1: snapshot.reserved_1(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::log::log_tests::gen_clock;
    use proptest::prelude::*;

    #[test]
    fn causal_snapshot_bytes_conversion() {
        let epoch = ProbeEpoch(2);
        let ticks = ProbeTicks(1);
        let snap = CausalSnapshot {
            clock: LogicalClock {
                id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
                epoch,
                ticks,
            },
            reserved_0: [0x34, 0x56],
            reserved_1: [0x78, 0x9A],
        };
        let max_id_le_bytes = ProbeId::MAX_ID.to_le_bytes();
        let epoch_le_bytes = epoch.0.to_le_bytes();
        let ticks_le_bytes = ticks.0.to_le_bytes();
        #[rustfmt::skip]
            let expected_bytes: [u8; 12] = [
            max_id_le_bytes[0], max_id_le_bytes[1], max_id_le_bytes[2], max_id_le_bytes[3],
            // Note that for historical reasons, the ticks
            // field precedes the epoch field in the current causal
            // snapshot wire format.
            ticks_le_bytes[0], ticks_le_bytes[1],
            epoch_le_bytes[0], epoch_le_bytes[1],
            0x34, 0x56,
            0x78, 0x9A
        ];
        assert_eq!(snap.to_le_bytes(), expected_bytes);
        assert_eq!(CausalSnapshot::from_le_bytes(expected_bytes).unwrap(), snap,);

        assert_eq!(
            CausalSnapshot::from_le_bytes([0u8; 12]),
            Err(InvalidProbeId)
        );
    }

    proptest! {
        #[test]
        fn round_trip_causal_snapshot(
            clock in gen_clock(),
            reserved_0 in proptest::num::u16::ANY,
            reserved_1 in proptest::num::u16::ANY) {
            let snap_in = CausalSnapshot {
                clock,
                reserved_0: reserved_0.to_le_bytes(),
                reserved_1: reserved_1.to_le_bytes(),
            };

            // Write out to new array variant
            let bytes = snap_in.to_le_bytes();
            let snap_out = CausalSnapshot::from_le_bytes(bytes).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);

            // Write out to extant slice variant
            let mut bytes = [0xFF; 12];
            let bytes_written = snap_in.write_into_le_bytes(&mut bytes[..]).unwrap();
            assert_eq!(bytes_written, size_of::<crate::CausalSnapshot>());
            let snap_out = CausalSnapshot::try_from(&bytes[..]).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);

            // Write out to extant exact-sized-array variant
            let mut bytes = [0xFF; 12];
            snap_in.write_into_le_bytes_exact(&mut bytes);
            assert_eq!(bytes_written, size_of::<crate::CausalSnapshot>());
            let snap_out = CausalSnapshot::try_from(&bytes).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);
        }
    }

    #[rustfmt::skip]
    static SNAPSHOT_BYTES: [u8; 12] = [
        // probe_id: 1
        0x01, 0x00, 0x00, 0x00,
        // clock ticks: 2
        0x02, 0x00,
        // epoch epoch: 3
        0x03, 0x00,
        // reserved_0: 4
        0x04, 0x00,
        // reserved_1: 5
        0x05, 0x00,
    ];

    #[test]
    fn min_buffer_len() {
        assert_eq!(WireCausalSnapshot::<&[u8]>::min_buffer_len(), 12);
    }

    #[test]
    fn construct() {
        let mut bytes = [0xFF; 12];
        let mut s = WireCausalSnapshot::new_unchecked(&mut bytes[..]);
        assert_eq!(s.check_len(), Ok(()));
        s.set_probe_id(ProbeId::new(1).unwrap());
        s.set_ticks(ProbeTicks(2));
        s.set_epoch(ProbeEpoch(3));
        s.set_reserved_0([0x04, 0x00]);
        s.set_reserved_1([0x05, 0x00]);
        assert_eq!(&s.into_inner()[..], &SNAPSHOT_BYTES[..]);
    }

    #[test]
    fn deconstruct() {
        let s = WireCausalSnapshot::new(&SNAPSHOT_BYTES[..]).unwrap();
        assert_eq!(s.probe_id().unwrap().get_raw(), 1);
        assert_eq!(s.ticks().0, 2);
        assert_eq!(s.epoch().0, 3);
        assert_eq!(s.reserved_0(), [0x04, 0x00]);
        assert_eq!(s.reserved_1(), [0x05, 0x00]);
    }

    #[test]
    fn missing_bytes() {
        let bytes = [0xFF; 12 - 1];
        assert_eq!(
            bytes.len(),
            WireCausalSnapshot::<&[u8]>::min_buffer_len() - 1
        );
        let s = WireCausalSnapshot::new(&bytes[..]);
        assert_eq!(s.unwrap_err(), MissingBytes);
    }
}
