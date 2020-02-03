//! ekotrace, a causal history tracing system
#![no_std]
#![deny(warnings)]
#![deny(missing_docs)]

use static_assertions::{assert_cfg, const_assert};
assert_cfg!(not(target_pointer_width = "16"));

mod compact_log;
mod error;
mod history;
mod id;

pub use error::*;
use history::DynamicHistory;
pub use id::*;

use core::convert::TryFrom;
use core::mem::size_of;
use slice_vec::slice_single::{embed, EmbedValueError, SplitUninitError};

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
#[derive(Copy, Clone, Default, Debug, Ord, PartialOrd, Eq, PartialEq)]
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
    #[allow(clippy::cast_ptr_alignment)]
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

    /// Produce a transmittable summary of this tracer's
    /// causal history for use by another Tracer elsewhere
    /// in the system.
    ///
    /// Pre-pruned to the causal history of just this node
    ///  and its immediate inbound neighbors.
    #[inline]
    pub fn distribute_fixed_size_snapshot(&mut self) -> Result<CausalSnapshot, DistributeError> {
        self.history.write_fixed_size_logical_clock()
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
}

impl<'a> Tracer for Ekotrace<'a> {
    #[inline]
    fn record_event(&mut self, event_id: EventId) {
        self.history.record_event(event_id);
    }

    #[inline]
    fn distribute_snapshot(&mut self, destination: &mut [u8]) -> Result<usize, DistributeError> {
        self.history.write_lcm_logical_clock(destination)
    }

    #[inline]
    fn merge_snapshot(&mut self, source: &[u8]) -> Result<(), MergeError> {
        self.history.merge_from_lcm_log_report_bytes(source)
    }

    #[inline]
    fn report(&mut self, destination: &mut [u8]) -> Result<usize, ReportError> {
        self.history.write_lcm_log_report(destination)
    }
}
