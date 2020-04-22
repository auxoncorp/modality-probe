//! ekotrace, a causal history tracing system
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings)]
#![deny(missing_docs)]

use static_assertions::{assert_cfg, const_assert};
assert_cfg!(not(target_pointer_width = "16"));

mod compact_log;
mod error;
mod history;
mod id;
mod macros;

pub use error::*;
use history::DynamicHistory;
pub use id::*;

use core::cmp::Ordering;
use core::convert::TryFrom;
use core::mem::size_of;
use fixed_slice_vec::single::{embed, EmbedValueError, SplitUninitError};

/// Fixed-sized snapshot of causal history for transmission around the system
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (TracerId, NonZero*) for C representation reasons.
#[repr(C)]
#[derive(Clone)]
pub struct CausalSnapshot {
    /// The tracer node at which this history snapshot was created
    pub tracer_id: u32,

    /// Mapping between tracer_ids and event-counts at each location
    pub clocks: [LogicalClock; 256],
    /// The number of clocks in the above `clocks` field that
    /// are populated with valid ids and counts
    pub clocks_len: u8,
}

/// A single logical clock, usable as an entry in a vector clock
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (TracerId, NonZero*) for C representation reasons.
#[derive(Copy, Clone, Default, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[repr(C)]
pub struct LogicalClock {
    /// The tracer node that this clock is tracking
    pub id: u32,
    /// Clock tick count
    pub count: u32,
}

/// Interface for the core (post-initialization) operations of `ekotrace`
pub trait Tracer {
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

    /// Write a summary of this tracer's causal history for use
    /// by another Tracer elsewhere in the system.
    ///
    /// This summary can be treated as an opaque blob of data
    /// that ought to be passed around to be `merge_snapshot`d, though
    /// it will conform to an internal schema for the interested.
    ///
    /// Pre-pruned to the causal history of just this node
    ///  and its immediate inbound neighbors.
    ///
    /// If the write was successful, returns the number of bytes written
    fn distribute_snapshot(&mut self, destination: &mut [u8]) -> Result<usize, DistributeError>;

    /// Consume a causal history summary structure provided
    /// by some other Tracer via `distribute_snapshot`.
    fn merge_snapshot(&mut self, source: &[u8]) -> Result<(), MergeError>;

    /// Conduct necessary background activities and write
    /// the recorded reporting log to a collection backend.
    ///
    /// Writes the Tracer's internal state according to the
    /// log reporting schema.
    ///
    /// If the write was successful, returns the number of bytes written
    fn report(&mut self, destination: &mut [u8]) -> Result<usize, ReportError>;
}

/// Reference implementation of an `ekotrace` tracer.
///
/// In addition to the standard `Tracer` API, it includes conveniences for:
/// * Recording events from primitive ids with just-in-time validation.
/// * Initialization with variable-sized memory backing.
/// * Can distribute and merge transparent fixed-sized snapshots in addition
/// to the opaque, arbitrarily-sized standard snapshots.
#[derive(Debug)]
#[repr(C)]
pub struct Ekotrace<'a> {
    history: &'a mut DynamicHistory<'a>,
}

impl<'a> Ekotrace<'a> {
    /// Initialize tracing for this location.
    /// `tracer_id` ought to be unique throughout the system,
    /// and must be greater than 0 and less than TracerId::MAX_ID.
    ///
    /// Returns a mutable reference to the tracer instance,
    /// which will be somewhere within the provided `memory`
    /// slice.
    ///
    /// This method is used to support completely opaque
    /// sizing of the tracer implementation, which simplifies
    /// use in C.
    ///
    /// Use `initialize_at` instead if you're working in Rust
    /// and want to use pre-validatated tracer ids.
    ///
    #[inline]
    pub fn try_initialize_at(
        memory: &'a mut [u8],
        tracer_id: u32,
    ) -> Result<&'a mut Ekotrace<'a>, InitializationError> {
        let tracer_id = TracerId::try_from(tracer_id)
            .map_err(|_: InvalidTracerId| InitializationError::InvalidTracerId)?;
        Ekotrace::initialize_at(memory, tracer_id).map_err(InitializationError::StorageSetupError)
    }
    /// Initialize tracing for this location.
    /// `tracer_id` ought to be unique throughout the system.
    ///
    /// Returns a mutable reference to the tracer instance,
    /// which will be somewhere within the provided `memory`
    /// slice.
    ///
    /// This method is used to support completely opaque
    /// sizing of the tracer implementation, which simplifies
    /// use in C.
    ///
    /// Use `new_with_storage` instead if you're working in Rust.
    #[inline]
    pub fn initialize_at(
        memory: &'a mut [u8],
        tracer_id: TracerId,
    ) -> Result<&'a mut Ekotrace<'a>, StorageSetupError> {
        match embed(memory, |history_memory| {
            Ekotrace::new_with_storage(history_memory, tracer_id)
        }) {
            Ok(v) => Ok(v),
            Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::Unalignable)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported)) => {
                const_assert!(size_of::<Ekotrace>() > 0);
                panic!("Static assertions ensure that this structure is not zero sized")
            }
            Err(EmbedValueError::ConstructionError(e)) => Err(e),
        }
    }

    /// Initialize tracing for this location,
    /// using `history_memory` for backing storage while
    /// returning a tracer instance on the stack.
    ///
    /// `tracer_id` ought to be unique throughout the system.
    #[inline]
    pub fn new_with_storage(
        history_memory: &'a mut [u8],
        tracer_id: TracerId,
    ) -> Result<Ekotrace<'a>, StorageSetupError> {
        let t = Ekotrace::<'a> {
            history: DynamicHistory::new_at(history_memory, tracer_id)?,
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

    /// Produce a transmittable summary of this tracer's
    /// causal history for use by another Tracer elsewhere
    /// in the system.
    ///
    /// Pre-pruned to the causal history of just this node
    ///  and its immediate inbound neighbors.
    #[inline]
    pub fn distribute_fixed_size_snapshot(&mut self) -> Result<CausalSnapshot, DistributeError> {
        self.history.write_fixed_size_snapshot()
    }

    /// Consume a fixed-sized causal history summary structure provided
    /// by some other Tracer.
    #[inline]
    pub fn merge_fixed_size_snapshot(
        &mut self,
        external_history: &CausalSnapshot,
    ) -> Result<(), MergeError> {
        self.history.merge_fixed_size(external_history)
    }

    /// Write a summary of this tracer's causal history, including the
    /// given opaque extension metadata, for use by another Tracer elsewhere in
    /// the system.
    ///
    /// This summary can be treated as an opaque blob of data that
    /// ought to be passed around to be `merge_snapshot`d, though it
    /// will conform to an internal schema for the interested.
    ///
    /// Pre-pruned to the causal history of just this node and its
    /// immediate inbound neighbors.
    ///
    /// If the write was successful, returns the number of bytes
    /// written
    pub fn distribute_snapshot_with_metadata(
        &mut self,
        destination: &mut [u8],
        meta: ExtensionBytes<'_>,
    ) -> Result<usize, DistributeError> {
        self.history
            .write_lcm_snapshot_with_metadata(destination, meta)
    }
    /// Consume a causal history summary structure provided
    /// by some other Tracer via `distribute_snapshot` or
    /// `distribute_snapshot_with_metadata` and return the extension
    /// metadata bytes for further custom processing.
    pub fn merge_snapshot_with_metadata<'d>(
        &mut self,
        source: &'d [u8],
    ) -> Result<ExtensionBytes<'d>, MergeError> {
        self.history.merge_from_lcm_snapshot_bytes(source)
    }
    /// Conduct necessary background activities and write
    /// the recorded reporting log to a collection backend,
    /// including arbitrary extension bytes provided.
    ///
    /// Writes the Tracer's internal state according to the
    /// log reporting schema.
    ///
    /// If the write was successful, returns the number of bytes written
    pub fn report_with_extension(
        &mut self,
        destination: &mut [u8],
        extension_metadata: ExtensionBytes<'_>,
    ) -> Result<usize, ReportError> {
        self.history
            .write_lcm_log_report(destination, extension_metadata)
    }

    /// Capture the current instance's moment in causal time
    /// for correlation with external systems.
    pub fn now(&self) -> EkotraceInstant {
        self.history.now()
    }
}

/// A situated moment in causal time.
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (TracerId, NonZero*) for C representation reasons.
#[derive(Debug, PartialEq, Hash)]
#[repr(C)]
pub struct EkotraceInstant {
    /// The current location's logical clock.
    /// `clock.id` should be equivalent to the id
    /// (a.k.a TracerId or location id) of the source `Ekotrace` instance
    pub clock: LogicalClock,
    /// How many events have been seen since the source instance
    /// reached the associated `clock`'s point in causal
    /// time.
    pub event_count: u32,
}

impl PartialOrd for EkotraceInstant {
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
/// the messages transmitted in this system (snapshots or
/// reports).
pub struct ExtensionBytes<'a>(pub &'a [u8]);

impl<'a> Tracer for Ekotrace<'a> {
    #[inline]
    fn record_event(&mut self, event_id: EventId) {
        self.history.record_event(event_id);
    }

    fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        self.history.record_event_with_payload(event_id, payload)
    }

    #[inline]
    fn distribute_snapshot(&mut self, destination: &mut [u8]) -> Result<usize, DistributeError> {
        self.distribute_snapshot_with_metadata(destination, ExtensionBytes(&[]))
    }

    #[inline]
    fn merge_snapshot(&mut self, source: &[u8]) -> Result<(), MergeError> {
        let _extension_bytes = self.merge_snapshot_with_metadata(source)?;
        Ok(())
    }

    #[inline]
    fn report(&mut self, destination: &mut [u8]) -> Result<usize, ReportError> {
        self.report_with_extension(destination, ExtensionBytes(&[]))
    }
}
