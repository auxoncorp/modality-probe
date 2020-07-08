//! Modality probe, a causal history tracing system
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]

use static_assertions::{assert_cfg, const_assert};
assert_cfg!(not(target_pointer_width = "16"));

pub mod compact_log;
mod error;
mod history;
mod id;
mod macros;
pub mod report;
pub mod wire;

pub use error::*;
use history::DynamicHistory;
pub use id::*;
pub use report::bulk::BulkReporter;
pub use report::chunked::ChunkedReporter;

use crate::report::chunked::{ChunkedReportError, ChunkedReportToken};
use core::cmp::Ordering;
use core::convert::TryFrom;
use core::mem::size_of;
use fixed_slice_vec::single::{embed, EmbedValueError, SplitUninitError};

/// Snapshot of causal history for transmission around the system.
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (ProbeId, NonZero*) for C representation reasons.
#[repr(C)]
#[derive(Clone)]
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
                let res_lsb = words[2] & core::u16::MAX as u32;
                let res_msb = (words[2] >> 16) & core::u16::MAX as u32;
                Ok(CausalSnapshot {
                    clock: LogicalClock {
                        id: probe_id,
                        count: words[1],
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
            self.clock.count,
            res_lsb | (res_msb << 16),
        ]
    }

    /// Writes a causal snapshot into a slice of little endian bytes
    pub fn write_into_le_bytes(&self, bytes: &mut [u8]) -> Result<(), wire::MissingBytes> {
        let mut wire = wire::WireCausalSnapshot::new_unchecked(bytes);
        wire.check_len()?;
        wire.set_probe_id(self.clock.id);
        wire.set_count(self.clock.count);
        wire.set_reserved_0(self.reserved_0);
        wire.set_reserved_1(self.reserved_1);
        Ok(())
    }
}

impl TryFrom<&[u8]> for CausalSnapshot {
    type Error = wire::CausalSnapshotWireError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let snapshot = wire::WireCausalSnapshot::new(bytes)?;
        Ok(CausalSnapshot {
            clock: LogicalClock {
                id: snapshot.probe_id()?,
                count: snapshot.count(),
            },
            reserved_0: snapshot.reserved_0(),
            reserved_1: snapshot.reserved_1(),
        })
    }
}

/// A single logical clock, usable as an entry in a vector clock
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[repr(C)]
pub struct LogicalClock {
    /// The probe that this clock is tracking
    /// Equivalent structurally to a u32.
    pub id: ProbeId,
    /// Clock tick count
    pub count: u32,
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

    /// Consume a causal history summary structure provided
    /// by some other probe via `produce_snapshot`.
    fn merge_snapshot(&mut self, external_history: &CausalSnapshot) -> Result<(), MergeError>;
}

/// Reference implementation of a `ModalityProbe`.
///
/// In addition to the standard `Probe` API, it includes conveniences for:
/// * Recording events from primitive ids with just-in-time validation.
/// * Initialization with variable-sized memory backing.
/// * Can produce and merge transparent snapshots
#[derive(Debug)]
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
    ) -> Result<&'a mut ModalityProbe<'a>, InitializationError> {
        let probe_id = ProbeId::try_from(probe_id)
            .map_err(|_: InvalidProbeId| InitializationError::InvalidProbeId)?;
        ModalityProbe::initialize_at(memory, probe_id)
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
    ) -> Result<&'a mut ModalityProbe<'a>, StorageSetupError> {
        match embed(memory, |history_memory| {
            ModalityProbe::new_with_storage(history_memory, probe_id)
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
    ) -> Result<ModalityProbe<'a>, StorageSetupError> {
        let t = ModalityProbe::<'a> {
            history: DynamicHistory::new_at(history_memory, probe_id)?,
        };
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
        if self.clock.id != other.clock.id {
            return None;
        }
        match self.clock.count.cmp(&other.clock.count) {
            Ordering::Equal => Some(self.event_count.cmp(&other.event_count)),
            o => Some(o),
        }
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
    fn merge_snapshot(&mut self, external_history: &CausalSnapshot) -> Result<(), MergeError> {
        self.history.merge_snapshot(external_history)
    }
}

impl<'a> BulkReporter for ModalityProbe<'a> {
    fn report_with_extension(
        &mut self,
        destination: &mut [u8],
        extension_metadata: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError> {
        self.history
            .report_with_extension(destination, extension_metadata)
    }
}

impl<'a> ChunkedReporter for ModalityProbe<'a> {
    fn start_chunked_report(&mut self) -> Result<ChunkedReportToken, ChunkedReportError> {
        self.history.start_chunked_report()
    }

    fn write_next_report_chunk(
        &mut self,
        token: &ChunkedReportToken,
        destination: &mut [u8],
    ) -> Result<usize, ChunkedReportError> {
        self.history.write_next_report_chunk(token, destination)
    }

    fn finish_chunked_report(
        &mut self,
        token: ChunkedReportToken,
    ) -> Result<(), ChunkedReportError> {
        self.history.finish_chunked_report(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compact_log::log_tests::*;
    use proptest::prelude::*;

    #[test]
    fn causal_snapshot_bytes_conversion() {
        let snap = CausalSnapshot {
            clock: LogicalClock {
                id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
                count: 0x2222_2222,
            },
            reserved_0: 0x3333,
            reserved_1: 0x4444,
        };
        assert_eq!(
            snap.to_le_bytes(),
            [ProbeId::MAX_ID, 0x2222_2222, 0x4444_3333]
        );

        assert_eq!(
            CausalSnapshot::from_le_bytes([ProbeId::MAX_ID, 0xBBBB_BBBB, 0xDDDD_CCCC]),
            Ok(CausalSnapshot {
                clock: LogicalClock {
                    id: ProbeId::new(ProbeId::MAX_ID).unwrap(),
                    count: 0xBBBB_BBBB,
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
            snap_in.write_into_le_bytes(&mut bytes[..]).unwrap();
            let snap_out = CausalSnapshot::try_from(&bytes[..]).unwrap();
            assert_eq!(snap_in.clock, snap_out.clock);
            assert_eq!(snap_in.reserved_0, snap_out.reserved_0);
            assert_eq!(snap_in.reserved_1, snap_out.reserved_1);
        }
    }
}
