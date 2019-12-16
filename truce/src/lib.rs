#![no_std]

/// Public interface to tracing.
#[repr(C)]
pub struct Tracer<'a> {
    node_id: u32,
    backend: &'a mut dyn Backend,
}

/// Public-but-opaque blob of causal history
#[repr(C)]
#[derive(Debug, PartialEq, PartialOrd)]
pub struct CausalHistory {
    // IntervalTreeClock or maybe BloomClock state goes here
// This is the publicly-visible-and-transmittable causal
// history structure, and is allowed to vary from the
// structure used internally by the tracer.
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
    /// `node_id` ought to be unique throughout the system.
    pub fn initialize(node_id: u32, backend: &'a mut dyn Backend) -> Self {
        unimplemented!()
    }

    /// Record that an event occurred. The end user is responsible
    /// for associating meaning with each event_id.
    pub fn record_event(&mut self, event_id: core::num::NonZeroU32) {
        unimplemented!()
    }

    /// Conduct necessary background activities, such as transmission
    /// of the the recorded events to a collection backend or
    /// optimization of local data.
    pub fn service(&mut self) {
        unimplemented!()
    }

    /// Produce a transmittable summary of this tracer's
    /// causal history for use by another Tracer elsewhere
    /// in the system.
    pub fn snapshot_history(&self) -> CausalHistory {
        unimplemented!()
    }

    /// Consume a causal history summary structure provided
    /// by some other Tracer.
    pub fn merge_history(external_history: CausalHistory) {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;

    #[test]
    fn tracer_lifecycle_does_not_panic() {
        let node_id = 1;

        struct DevNull;
        impl Backend for DevNull {
            fn send_tracer_data(&mut self, _data: &[u8]) -> bool {
                true
            }
        }

        let mut backend = DevNull;
        let mut tracer = Tracer::initialize(node_id, &mut backend);
        let event_a = NonZeroU32::new(2).expect("Should be non-zero");
        let event_b = NonZeroU32::new(3).expect("Should be non-zero");

        let q = tracer.snapshot_history();
        tracer.record_event(event_a);
        let r = tracer.snapshot_history();
        assert!(q < r);
        assert_ne!(q, r);
        tracer.record_event(event_a);
        let s = tracer.snapshot_history();
        assert!(r < s);
        assert_ne!(r, s);
        tracer.record_event(event_b);
        let t = tracer.snapshot_history();
        assert!(s < t);
        assert_ne!(s, t);
        tracer.record_event(event_a);
        let u = tracer.snapshot_history();
        assert!(t < u);
        assert_ne!(t, u);
        tracer.service();
        let v = tracer.snapshot_history();
        // Should service calls affect the outcome of snapshot_history()?
        assert!(u < v);
        assert_ne!(u, v);
    }
}
