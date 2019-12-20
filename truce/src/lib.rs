#![no_std]

use static_assertions::assert_cfg;
assert_cfg!(not(target_pointer_width = "16"));

mod history;

use history::DynamicHistory;

use core::mem::{align_of, size_of};
use core::num::NonZeroU32;

pub const BACKEND_SEND_SUCCESSFUL_EVENT: EventId = EventId(unsafe { NonZeroU32::new_unchecked(1) });
pub const MERGE_INBAND_CAUSALITY_EVENT: EventId = EventId(unsafe { NonZeroU32::new_unchecked(2) });
pub const SHARED_INBAND_CAUSALITY_EVENT: EventId = EventId(unsafe { NonZeroU32::new_unchecked(3) });

/// Snapshot of causal history for transmission around the system
///
/// Note the use of bare integer types rather than the safety-oriented
/// wrappers (TracerId, NonZero*) for C representation reasons.
#[repr(C)]
#[derive(Clone)]
pub struct CausalSnapshot {
    /// The tracer node at which this history snapshot was created
    pub tracer_id: u32,

    /// Mapping between tracer_ids and event-counts at each location
    pub buckets: [LogicalClockBucket; 256],
    pub buckets_len: u8,
}

#[derive(Copy, Clone, Default, Debug, Ord, PartialOrd, Eq, PartialEq)]
#[repr(C)]
pub struct LogicalClockBucket {
    /// The tracer node that this clock is tracking
    pub id: u32,
    /// Clock tick count
    pub count: u32,
}

/// Ought to uniquely identify a location for where events occur within a system under test.
///
/// Typically represents a single thread.
///
/// Must be backed by a value greater than 0 and less than 0b1000_0000_0000_0000
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TracerId(NonZeroU32);

impl TracerId {
    const MAX_RAW_ID: u32 = 0b0111_1111_1111_1111;

    /// raw_id must be greater than 0 and less than 0b1000_0000_0000_0000
    #[inline]
    pub fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_RAW_ID {
            return None;
        }
        NonZeroU32::new(raw_id).map(|id| Self(id))
    }

    #[inline]
    pub fn get(&self) -> NonZeroU32 {
        self.0
    }

    #[inline]
    pub fn get_raw(&self) -> u32 {
        self.0.get()
    }
}

/// Uniquely identify an event or kind of event.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct EventId(NonZeroU32);

impl EventId {
    const MAX_RAW_ID: u32 = 0b0111_1111_1111_1111;

    /// raw_id must be greater than 0 and less than 0b1000_0000_0000_0000
    #[inline]
    pub fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_RAW_ID {
            return None;
        }
        NonZeroU32::new(raw_id).map(|id| Self(id))
    }

    #[inline]
    pub fn get(&self) -> NonZeroU32 {
        self.0
    }

    #[inline]
    pub fn get_raw(&self) -> u32 {
        self.0.get()
    }
}

#[derive(Debug)]
pub enum LocalStorageCreationError {
    UnderMinimumAllowedSize,
    ExceededMaximumAddressableSize,
    NullDestination,
}

/// Public interface to tracing.
#[derive(Debug)]
#[repr(C)]
pub struct Tracer<'a, 'b> {
    id: TracerId,
    history: &'a mut DynamicHistory,
    backend: &'b mut dyn Backend,
}

/// Trace data collection interface
pub trait Backend: core::fmt::Debug {
    /// Transmits a Tracer's internal state according to the
    /// tracing data protocol to some storage or presentation
    /// or retransmission backend.
    ///
    /// Returns `true` if the data was successfully transmitted
    fn send_tracer_data(&mut self, data: &[u8]) -> bool;
}

impl<'a, 'b> Tracer<'a, 'b> {
    /// Initialize tracing for this location.
    /// `tracer_id` ought to be unique throughout the system.
    pub fn initialize_at(
        memory: &'a mut [u8],
        tracer_id: TracerId,
        backend: &'b mut dyn Backend,
    ) -> Result<&'a mut Tracer<'a, 'b>, LocalStorageCreationError> {
        let tracer_align_offset = memory
            .as_mut_ptr()
            .align_offset(align_of::<Tracer<'_, '_>>());
        let tracer_bytes = tracer_align_offset + size_of::<Tracer<'_, '_>>();
        if tracer_bytes > memory.len() {
            return Err(LocalStorageCreationError::UnderMinimumAllowedSize);
        }
        let tracer_ptr =
            unsafe { memory.as_mut_ptr().add(tracer_align_offset) as *mut Tracer<'_, '_> };
        unsafe {
            *tracer_ptr =
                Tracer::new_with_storage(&mut memory[tracer_bytes..], tracer_id, backend)?;
            Ok(tracer_ptr
                .as_mut()
                .expect("Tracer pointer should not be null"))
        }
    }

    pub fn new_with_storage(
        history_memory: &'a mut [u8],
        tracer_id: TracerId,
        backend: &'b mut dyn Backend,
    ) -> Result<Tracer<'a, 'b>, LocalStorageCreationError> {
        let t = Tracer::<'a, 'b> {
            id: tracer_id,
            history: DynamicHistory::new_at(history_memory, tracer_id)?,
            backend,
        };
        Ok(t)
    }

    /// Record that an event occurred. The end user is responsible
    /// for associating meaning with each event_id.
    #[inline]
    pub fn record_event(&mut self, event_id: EventId) {
        self.history.record_event(event_id);
    }

    /// Conduct necessary background activities, such as transmission
    /// of the the recorded events to a collection backend or
    /// optimization of local data.
    pub fn service(&mut self) {
        self.history.send_to_backend(self.backend);
    }

    /// Produce a transmittable summary of this tracer's
    /// causal history for use by another Tracer elsewhere
    /// in the system.
    ///
    /// Pre-pruned to the causal history of just this node
    ///  and its immediate inbound neighbors.
    pub fn snapshot(&mut self) -> CausalSnapshot {
        self.history.snapshot()
    }

    /// Convenience function that the end user can press when they
    /// manage to transmit a snapshot to another part of the system
    pub fn record_snapshot_shared(&mut self) {
        self.record_event(SHARED_INBAND_CAUSALITY_EVENT)
    }

    /// Consume a causal history summary structure provided
    /// by some other Tracer.
    pub fn merge_history(&mut self, external_history: &CausalSnapshot) {
        self.history.merge(external_history);
    }
}
