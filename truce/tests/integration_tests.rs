use core::num::NonZeroU32;
use truce::*;
struct DevNull;
impl Backend for DevNull {
    fn send_tracer_data(&mut self, _data: &[u8]) -> bool {
        true
    }
}

#[test]
fn tracer_lifecycle_does_not_panic() {
    let tracer_id = TracerId(NonZeroU32::new(1).expect("Could not make tracer_id"));

    let mut backend = DevNull;
    let mut tracer = Tracer::initialize(tracer_id, &mut backend);
    let event_a = EventId(NonZeroU32::new(2).expect("Should be non-zero"));
    let event_b = EventId(NonZeroU32::new(3).expect("Should be non-zero"));

    let p = tracer.snapshot_history();
    let q = tracer.snapshot_history();
    assert_eq!(p, q);
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

#[test]
fn round_trip_merge_snapshot() {
    let tracer_id = TracerId(NonZeroU32::new(1).expect("Could not make tracer_id"));

    let mut backend = DevNull;
    let mut tracer = Tracer::initialize(tracer_id, &mut backend);
    let event_a = EventId(NonZeroU32::new(2).expect("Should be non-zero"));
    tracer.record_event(event_a);
    let snapshot_a = tracer.snapshot_history();

    // Re-initialize a tracer with no previous history
    let mut backend = DevNull;
    let mut tracer_dupe = Tracer::initialize(tracer_id, &mut backend);
    tracer_dupe.merge_history(snapshot_a.clone());
    let snapshot_b = tracer_dupe.snapshot_history();

    assert_eq!(snapshot_a, snapshot_b);

    tracer.record_event(event_a);
    let snapshot_c = tracer.snapshot_history();
    assert_ne!(snapshot_c, snapshot_a);
    assert_ne!(snapshot_c, snapshot_b);
    assert!(snapshot_a < snapshot_c);
    assert!(snapshot_b < snapshot_c);

    tracer_dupe.merge_history(snapshot_c);

    assert_eq!(
        tracer_dupe.snapshot_history(),
        tracer.snapshot_history(),
        "After merging, the contents should be the same"
    );
}
