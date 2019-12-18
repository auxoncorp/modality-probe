#![no_std]

mod history;

use history::History;

use core::num::NonZeroU32;

pub const BACKEND_TRANSMISSION_SUCCESSFUL_EVENT: EventId =
    EventId(unsafe { NonZeroU32::new_unchecked(1) });

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

#[repr(C)]
#[derive(Copy, Clone, Default, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct LogicalClockBucket {
    pub id: u32,
    pub count: u32,
}

/// Ought to uniquely identify a location for where events occur within a system under test.
///
/// Typically represents a single thread.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TracerId(pub NonZeroU32);

/// Uniquely identify an event or kind of event.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct EventId(pub NonZeroU32);

/// Public interface to tracing.
#[repr(C)]
pub struct Tracer<'a> {
    id: TracerId,
    backend: &'a mut dyn Backend,
    history: History,
}

/// Trace data collection interface
pub trait Backend {
    /// Transmits a Tracer's internal state according to the
    /// tracing data protocol to some storage or presentation
    /// or retransmission backend.
    ///
    /// Returns `true` if the data was successfully transmitted
    fn send_tracer_data(&mut self, data: &[u8]) -> bool;
}

impl<'a> Tracer<'a> {
    /// Initialize tracing for this location.
    /// `tracer_id` ought to be unique throughout the system.
    pub fn initialize(tracer_id: TracerId, backend: &'a mut dyn Backend) -> Self {
        Tracer::<'a> {
            id: tracer_id,
            backend,
            history: History::new(tracer_id),
        }
    }

    /// Record that an event occurred. The end user is responsible
    /// for associating meaning with each event_id.
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
    /// TODO - where to implement pruning of history for transmission
    pub fn snapshot_history(&mut self) -> CausalSnapshot {
        self.history.snapshot()
    }

    /// Consume a causal history summary structure provided
    /// by some other Tracer.
    pub fn merge_history(&mut self, external_history: CausalSnapshot) {
        self.history.merge(external_history);
    }
}
