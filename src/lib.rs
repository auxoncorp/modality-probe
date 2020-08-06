//! Modality probe, a causal history tracing system

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]
#![allow(clippy::unit_arg)]
assert_cfg!(not(target_pointer_width = "16"));

use core::{
    cmp::{max, Ordering},
    convert::TryFrom,
    mem::size_of,
    num::NonZeroUsize,
};

use fixed_slice_vec::single::{embed, EmbedValueError, SplitUninitError};
#[cfg(feature = "std")]
use proptest_derive::Arbitrary;
use static_assertions::{assert_cfg, const_assert};

pub use error::*;
use history::DynamicHistory;
pub use id::*;
pub use restart_counter::{
    next_sequence_id_fn, CRestartCounterProvider, RestartCounter, RestartCounterProvider,
    RustRestartCounterProvider,
};

mod error;
mod history;
mod id;
pub mod log;
mod macros;
mod restart_counter;
mod ring;
pub mod wire;

/// Snapshot of causal history for transmission around the system.
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (ProbeId, NonZero*) for C representation reasons.
#[repr(C)]
#[derive(Clone, Debug)]
pub struct CausalSnapshot {
    /// Probe id and tick-count at the probe which this history snapshot
    /// was created from
    pub clock: LogicalClock,
    /// Reserved field
    pub reserved_0: u16,
    /// Reserved field
    pub reserved_1: u16,
}

impl CausalSnapshot {
    /// Construct a causal snapshot from a sequence of little endian bytes
    pub fn from_le_bytes(words: [u32; 3]) -> Result<Self, InvalidProbeId> {
        match ProbeId::new(words[0]) {
            None => Err(InvalidProbeId),
            Some(probe_id) => {
                let (epoch, ticks) = unpack_clock_word(words[1]);
                let res_lsb = words[2] & core::u16::MAX as u32;
                let res_msb = (words[2] >> 16) & core::u16::MAX as u32;
                Ok(CausalSnapshot {
                    clock: LogicalClock {
                        id: probe_id,
                        ticks,
                        epoch,
                    },
                    reserved_0: res_lsb as u16,
                    reserved_1: res_msb as u16,
                })
            }
        }
    }

    /// Return a causal snapshot as a sequence of little endian bytes
    pub fn to_le_bytes(&self) -> [u32; 3] {
        let res_lsb = self.reserved_0 as u32;
        let res_msb = self.reserved_1 as u32;
        [
            self.clock.id.get_raw(),
            pack_clock_word(self.clock.epoch, self.clock.ticks),
            res_lsb | (res_msb << 16),
        ]
    }

    /// Writes a causal snapshot into a slice of little endian bytes.
    ///
    /// Returns the number of bytes written.
    pub fn write_into_le_bytes(&self, bytes: &mut [u8]) -> Result<usize, wire::MissingBytes> {
        let mut wire = wire::WireCausalSnapshot::new_unchecked(bytes);
        wire.check_len()?;
        wire.set_probe_id(self.clock.id);
        wire.set_ticks(self.clock.ticks);
        wire.set_epoch(self.clock.epoch);
        wire.set_reserved_0(self.reserved_0);
        wire.set_reserved_1(self.reserved_1);
        Ok(wire::WireCausalSnapshot::<&[u8]>::min_buffer_len())
    }
}

impl TryFrom<&[u8]> for CausalSnapshot {
    type Error = wire::CausalSnapshotWireError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let snapshot = wire::WireCausalSnapshot::new(bytes)?;
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

impl PartialEq for CausalSnapshot {
    fn eq(&self, other: &Self) -> bool {
        self.clock == other.clock
    }
}

impl PartialOrd for CausalSnapshot {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.clock.partial_cmp(&other.clock)
    }
}

/// The epoch part of a probe's logical clock
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "std", derive(Arbitrary))]
pub struct ProbeEpoch(pub u16);

impl ProbeEpoch {
    /// The maximum value a probe epoch can inhabit.
    pub const MAX: Self = ProbeEpoch(u16::MAX);
    const WRAPAROUND_THRESHOLD_TOP: Self = ProbeEpoch(u16::MAX - 3);
    const WRAPAROUND_THRESHOLD_BOTTOM: Self = ProbeEpoch(3);

    /// u16::overflowing_add, on the inner value
    pub fn overflowing_add(self, n: u16) -> (ProbeEpoch, bool) {
        let (n, overflow) = self.0.overflowing_add(n);
        (n.into(), overflow)
    }
}

impl From<u16> for ProbeEpoch {
    fn from(x: u16) -> Self {
        ProbeEpoch(x)
    }
}

impl From<ProbeEpoch> for u16 {
    fn from(e: ProbeEpoch) -> Self {
        e.0
    }
}

/// The clock part of a probe's logical clock
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "std", derive(Arbitrary))]
pub struct ProbeTicks(pub u16);

impl ProbeTicks {
    /// The maximum value a probe tick can inhabit.
    pub const MAX: Self = ProbeTicks(u16::MAX);
}

impl From<u16> for ProbeTicks {
    fn from(ticks: u16) -> Self {
        ProbeTicks(ticks)
    }
}

impl From<ProbeTicks> for u16 {
    fn from(t: ProbeTicks) -> Self {
        t.0
    }
}

/// Pack the epoch and clock into a u32
#[inline]
pub fn pack_clock_word(epoch: ProbeEpoch, ticks: ProbeTicks) -> u32 {
    ((epoch.0 as u32) << 16) | (ticks.0 as u32)
}

/// Unpack a probe epoch and clock from a u32
#[inline]
pub fn unpack_clock_word(w: u32) -> (ProbeEpoch, ProbeTicks) {
    let epoch = (w >> 16) & (core::u16::MAX as u32);
    let ticks = w & (core::u16::MAX as u32);
    (ProbeEpoch(epoch as u16), ProbeTicks(ticks as u16))
}

/// A single logical clock, usable as an entry in a vector clock
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[repr(C)]
pub struct LogicalClock {
    /// The probe that this clock is tracking
    /// Equivalent structurally to a u32.
    pub id: ProbeId,

    /// The epoch portion of the logical clock
    pub epoch: ProbeEpoch,

    /// The clock portion of the logical clock
    pub ticks: ProbeTicks,
}

impl PartialOrd for LogicalClock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.id != other.id {
            None
        } else {
            (self.epoch, self.ticks).partial_cmp(&(other.epoch, other.ticks))
        }
    }
}

/// A wraparound-aware ordering comparison helper
/// for the clock components.
#[derive(PartialEq, Eq)]
pub struct OrdClock(pub ProbeEpoch, pub ProbeTicks);

impl PartialOrd for OrdClock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if (self.0, self.1) == (other.0, other.1) {
            Some(Ordering::Equal)
        } else if (self.0, self.1) > (other.0, other.1)
            || (other.0 >= ProbeEpoch::WRAPAROUND_THRESHOLD_TOP
                && self.0 <= ProbeEpoch::WRAPAROUND_THRESHOLD_BOTTOM)
        {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Less)
        }
    }
}

impl LogicalClock {
    /// Increment the logical clock by one. If the clock portion overflows,
    /// clock wraps around and epoch is incremented. Epoch and clock both wrap
    /// around to 1.
    ///
    /// Returns true if the clock portion did overflow, otherwise returns false.
    #[inline]
    pub fn increment(&mut self) -> bool {
        let (new_clock, overflow) = self.ticks.0.overflowing_add(1);
        self.ticks = ProbeTicks(max(new_clock, 1));
        if overflow {
            self.epoch = ProbeEpoch(self.epoch.0.wrapping_add(1));
        }

        // This handles both wrapping around to 1 and going from the zero epoch
        // (uninitialized) to epoch 1
        self.epoch = ProbeEpoch(max(self.epoch.0, 1));
        overflow
    }

    /// Put the clock into a byte array, probe id first, where the two
    /// u32's are unpacked as little endian bytes.
    pub fn to_le_bytes(&self) -> [u8; 8] {
        let mut out = [0; 8];
        out[..4].copy_from_slice(&self.id.get_raw().to_le_bytes());
        out[4..].copy_from_slice(&pack_clock_word(self.epoch, self.ticks).to_le_bytes());
        out
    }
}

/// Interface for the core (post-initialization) operations of `ModalityProbe`
pub trait Probe {
    /// Record that an event occurred. The end user is responsible
    /// for associating meaning with each event_id.
    ///
    /// Accepts an event_id pre-validated to be within the acceptable
    /// range.
    fn record_event(&mut self, event_id: EventId);

    /// Record that an event occurred with a `u32`'s width's worth (4
    /// bytes) of context via `payload`. The end user is responsible for
    /// associating meaning with each event_id.
    ///
    /// Accepts an event_id pre-validated to be within the acceptable
    /// range.
    fn record_event_with_payload(&mut self, event_id: EventId, payload: u32);

    /// Write a summary of this probe's causal history for use
    /// by another probe elsewhere in the system.
    fn produce_snapshot(&mut self) -> Result<CausalSnapshot, ProduceError>;

    /// Write a summary of this probe's causal history for use
    /// by another probe elsewhere in the system.
    ///
    /// This summary can be treated as an opaque blob of data
    /// that ought to be passed around to be `merge_snapshot`d, though
    /// it will conform to an internal schema for the interested.
    ///
    /// If the write was successful, returns the number of bytes written.
    fn produce_snapshot_bytes(&mut self, destination: &mut [u8]) -> Result<usize, ProduceError>;

    /// Consume a causal history summary structure provided
    /// by some other probe via `produce_snapshot`.
    fn merge_snapshot(&mut self, external_history: &CausalSnapshot) -> Result<(), MergeError>;

    /// Consume a causal history summary blob provided
    /// by some other probe via `produce_snapshot_bytes`.
    fn merge_snapshot_bytes(&mut self, source: &[u8]) -> Result<(), MergeError>;

    /// Copies a wire-ready report into `destination`.
    ///
    /// A wire-ready report is a byte slice containing:
    /// 1. A wire header.
    /// 2. The most up to date clocks the probe has seen but not yet
    ///    reported.
    /// 3. As much of the event log that will fit in the remaining
    ///    chunk of `destination`.
    fn report(&mut self, destination: &mut [u8]) -> Result<Option<NonZeroUsize>, ReportError>;
}

/// Reference implementation of a `ModalityProbe`.
///
/// In addition to the standard `Probe` API, it includes conveniences for:
/// * Recording events from primitive ids with just-in-time validation.
/// * Initialization with variable-sized memory backing.
/// * Can produce and merge transparent snapshots
#[repr(C)]
pub struct ModalityProbe<'a> {
    history: &'a mut DynamicHistory<'a>,
}

impl<'a> ModalityProbe<'a> {
    /// Initialize a probe for this probe id.
    /// `probe_id` ought to be unique throughout the system,
    /// and must be greater than 0 and less than ProbeId::MAX_ID.
    ///
    /// Returns a mutable reference to the probe instance,
    /// which will be somewhere within the provided `memory`
    /// slice.
    ///
    /// This method is used to support completely opaque
    /// sizing of the probe implementation, which simplifies
    /// use in C.
    ///
    /// Use `initialize_at` instead if you're working in Rust
    /// and want to use pre-validatated probe ids.
    ///
    #[inline]
    pub fn try_initialize_at(
        memory: &'a mut [u8],
        probe_id: u32,
        restart_counter: RestartCounterProvider<'a>,
    ) -> Result<&'a mut ModalityProbe<'a>, InitializationError> {
        let probe_id = ProbeId::try_from(probe_id)
            .map_err(|_: InvalidProbeId| InitializationError::InvalidProbeId)?;
        ModalityProbe::initialize_at(memory, probe_id, restart_counter)
            .map_err(InitializationError::StorageSetupError)
    }

    /// Initialize a probe for this probe id.
    /// `probe_id` ought to be unique throughout the system.
    ///
    /// Returns a mutable reference to the probe instance,
    /// which will be somewhere within the provided `memory`
    /// slice.
    ///
    /// This method is used to support completely opaque
    /// sizing of the probe implementation, which simplifies
    /// use in C.
    ///
    /// Use `new_with_storage` instead if you're working in Rust.
    #[inline]
    pub fn initialize_at(
        memory: &'a mut [u8],
        probe_id: ProbeId,
        restart_counter: RestartCounterProvider<'a>,
    ) -> Result<&'a mut ModalityProbe<'a>, StorageSetupError> {
        match embed(memory, |history_memory| {
            ModalityProbe::new_with_storage(history_memory, probe_id, restart_counter)
        }) {
            Ok(v) => Ok(v),
            Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::Unalignable)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported)) => {
                const_assert!(size_of::<ModalityProbe>() > 0);
                panic!("Static assertions ensure that this structure is not zero sized")
            }
            Err(EmbedValueError::ConstructionError(e)) => Err(e),
        }
    }

    /// Initialize a probe for this probe id,
    /// using `history_memory` for backing storage while
    /// returning a probe instance on the stack.
    ///
    /// `probe_id` ought to be unique throughout the system.
    #[inline]
    pub fn new_with_storage(
        history_memory: &'a mut [u8],
        probe_id: ProbeId,
        restart_counter: RestartCounterProvider<'a>,
    ) -> Result<ModalityProbe<'a>, StorageSetupError> {
        let mut t = ModalityProbe::<'a> {
            history: DynamicHistory::new_at(history_memory, probe_id, restart_counter)?,
        };
        t.record_event_with_payload(
            EventId::EVENT_PROBE_INITIALIZED,
            t.history.probe_id.get_raw(),
        );
        Ok(t)
    }

    /// Record that an event occurred. The end user is responsible
    /// for associating meaning with each event_id.
    ///
    /// Accepts a primitive event_id and
    /// returns an error if the event_id was discovered
    /// to be invalid.
    ///
    /// If you're working in Rust and want type assurances around
    /// id kinds or want to avoid the performance penalty of id validation
    /// every call, use `record_event` instead.
    #[inline]
    pub fn try_record_event(&mut self, event_id: u32) -> Result<(), InvalidEventId> {
        let event_id = EventId::try_from(event_id)?;
        self.history.record_event(event_id);
        Ok(())
    }

    /// Record that an event occurred and associate some context with
    /// via a 4-byte payload, `payload`. The end user is responsible for
    /// associating meaning with each event_id.
    ///
    /// Accepts a primitive event_id and returns an error if the
    /// event_id was discovered to be invalid.
    ///
    /// If you're working in Rust and want type assurances around id
    /// kinds or want to avoid the performance penalty of id
    /// validation every call, use `record_event_with_payload`
    /// instead.
    #[inline]
    pub fn try_record_event_with_payload(
        &mut self,
        event_id: u32,
        payload: u32,
    ) -> Result<(), InvalidEventId> {
        let event_id = EventId::try_from(event_id)?;
        self.history.record_event_with_payload(event_id, payload);
        Ok(())
    }

    /// Capture the current instance's moment in causal time
    /// for correlation with external systems.
    pub fn now(&self) -> ModalityProbeInstant {
        self.history.now()
    }
}

/// A situated moment in causal time.
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (ProbeId, NonZero*) for C representation reasons.
#[derive(Debug, PartialEq, Hash)]
#[repr(C)]
pub struct ModalityProbeInstant {
    /// The current probe's logical clock.
    /// `clock.id` should be equivalent to the probe id
    /// of the source `ModalityProbe` instance
    pub clock: LogicalClock,
    /// How many events have been seen since the source instance
    /// reached the associated `clock`'s point in causal
    /// time.
    pub event_count: u32,
}

impl PartialOrd for ModalityProbeInstant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.clock, self.event_count).partial_cmp(&(other.clock, other.event_count))
    }
}

/// Raw bytes related to extension metadata stored alongside
/// the messages transmitted in this system (reports).
#[derive(Debug)]
pub struct ExtensionBytes<'a>(pub &'a [u8]);

impl<'a> Probe for ModalityProbe<'a> {
    #[inline]
    fn record_event(&mut self, event_id: EventId) {
        self.history.record_event(event_id);
    }

    #[inline]
    fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        self.history.record_event_with_payload(event_id, payload)
    }

    #[inline]
    fn produce_snapshot(&mut self) -> Result<CausalSnapshot, ProduceError> {
        self.history.produce_snapshot()
    }

    #[inline]
    fn produce_snapshot_bytes(&mut self, destination: &mut [u8]) -> Result<usize, ProduceError> {
        self.history.produce_snapshot_bytes(destination)
    }

    #[inline]
    fn merge_snapshot(&mut self, external_history: &CausalSnapshot) -> Result<(), MergeError> {
        self.history.merge_snapshot(external_history)
    }

    #[inline]
    fn merge_snapshot_bytes(&mut self, source: &[u8]) -> Result<(), MergeError> {
        self.history.merge_snapshot_bytes(source)
    }

    #[inline]
    fn report(&mut self, destination: &mut [u8]) -> Result<Option<NonZeroUsize>, ReportError> {
        self.history.report(destination)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::log::log_tests::gen_clock;
    use proptest::prelude::*;

    #[test]
    fn causal_snapshot_bytes_conversion() {
        let snap = CausalSnapshot {
            clock: LogicalClock {
                id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
                epoch: ProbeEpoch(2),
                ticks: ProbeTicks(1),
            },
            reserved_0: 0x3333,
            reserved_1: 0x4444,
        };
        assert_eq!(
            snap.to_le_bytes(),
            [ProbeId::MAX_ID, 0x0002_0001, 0x4444_3333]
        );

        assert_eq!(
            CausalSnapshot::from_le_bytes([ProbeId::MAX_ID, 0xAAAA_BBBB, 0xDDDD_CCCC]),
            Ok(CausalSnapshot {
                clock: LogicalClock {
                    id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
                    epoch: ProbeEpoch(0xAAAA),
                    ticks: ProbeTicks(0xBBBB),
                },
                reserved_0: 0xCCCC,
                reserved_1: 0xDDDD,
            })
        );

        assert_eq!(
            CausalSnapshot::from_le_bytes([0, 0xBBBB_BBBB, 0xDDDD_CCCC]),
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
                reserved_0,
                reserved_1,
            };

            let bytes = snap_in.to_le_bytes();
            let snap_out = CausalSnapshot::from_le_bytes(bytes).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);

            let mut bytes = [0xFF; 12];
            let bytes_written = snap_in.write_into_le_bytes(&mut bytes[..]).unwrap();
            assert_eq!(bytes_written, size_of::<crate::CausalSnapshot>());
            let snap_out = CausalSnapshot::try_from(&bytes[..]).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);
        }
    }

    #[test]
    fn logical_clock_ordering() {
        let lc =
            |id: ProbeId, epoch: ProbeEpoch, ticks: ProbeTicks| LogicalClock { id, epoch, ticks };

        let probe_a = ProbeId::new(1).unwrap();
        let probe_b = ProbeId::new(2).unwrap();

        // Clocks from different probes are not comparable
        proptest!(
            ProptestConfig::default(),
            |(epoch_a: ProbeEpoch, ticks_a: ProbeTicks, epoch_b: ProbeEpoch, ticks_b: ProbeTicks)| {
                prop_assert_eq!(lc(probe_a, epoch_a, ticks_a).partial_cmp(&lc(probe_b, epoch_b, ticks_b)),
                                None);
            }
        );

        // From the same probe, epoch takes precedence
        proptest!(
            ProptestConfig::default(),
            |(epoch_a1: ProbeEpoch, epoch_a2: ProbeEpoch, ticks_a1: ProbeTicks, ticks_a2: ProbeTicks)| {
                let cmp_res = lc(probe_a, epoch_a1, ticks_a1).partial_cmp(&lc(probe_a, epoch_a2, ticks_a2));
                if epoch_a1 == epoch_a2 {
                    prop_assert_eq!(cmp_res, ticks_a1.partial_cmp(&ticks_a2));
                } else {
                   prop_assert_eq!(cmp_res, epoch_a1.partial_cmp(&epoch_a2));
                }

            }
        );

        // Focused test for equal epochs
        proptest!(
            ProptestConfig::default(),
            |(epoch_a: ProbeEpoch, ticks_a1: ProbeTicks, ticks_a2: ProbeTicks)| {
                let cmp_res = lc(probe_a, epoch_a, ticks_a1).partial_cmp(&lc(probe_a, epoch_a, ticks_a2));
                prop_assert_eq!(cmp_res, ticks_a1.partial_cmp(&ticks_a2));
            }
        );
    }

    fn oc_cmp_eq(ordering: Ordering, left: (u16, u16), right: (u16, u16)) {
        assert_eq!(
            Some(ordering),
            OrdClock(left.0.into(), left.1.into())
                .partial_cmp(&OrdClock(right.0.into(), right.1.into()))
        )
    }

    #[test]
    fn ord_clock_basics() {
        // Symmetrical ordering
        use Ordering::*;
        oc_cmp_eq(Equal, (0, 0), (0, 0));
        oc_cmp_eq(Equal, (1, 1), (1, 1));
        oc_cmp_eq(Equal, (2, 2), (2, 2));

        oc_cmp_eq(Greater, (0, 1), (0, 0));
        oc_cmp_eq(Greater, (0, 2), (0, 0));
        oc_cmp_eq(Greater, (0, 2), (0, 1));

        oc_cmp_eq(Greater, (1, 0), (0, 0));
        oc_cmp_eq(Greater, (2, 0), (0, 0));
        oc_cmp_eq(Greater, (2, 0), (1, 0));

        oc_cmp_eq(Less, (0, 0), (0, 1));
        oc_cmp_eq(Less, (0, 0), (0, 2));

        oc_cmp_eq(Less, (0, 0), (1, 0));
        oc_cmp_eq(Less, (0, 0), (2, 0));
        oc_cmp_eq(Less, (1, 0), (2, 0));

        // Consider epoch first and foremost, and ticks only when epochs are equal.
        oc_cmp_eq(Greater, (1, 1), (0, 99));
        oc_cmp_eq(Less, (1, 99), (2, 0));

        // When one epoch is near the bottom of the range and the other is near the top,
        // we assume that the epoch near the bottom has wrapped around (and is actually ahead)
        oc_cmp_eq(Greater, (0, 0), (core::u16::MAX, 0));
        for left in 0..=ProbeEpoch::WRAPAROUND_THRESHOLD_BOTTOM.0 {
            for right in ProbeEpoch::WRAPAROUND_THRESHOLD_TOP.0..core::u16::MAX {
                // In this narrow range, even though the underlying numerical epoch value
                // of the left is less than that of the right, it is considered greater due
                // to wraparound awareness
                assert!(left < right);
                oc_cmp_eq(Greater, (left, 0), (right, 0));
            }
        }
    }
}
