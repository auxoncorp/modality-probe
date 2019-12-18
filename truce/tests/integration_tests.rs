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

    let p = tracer.snapshot();
    let q = tracer.snapshot();
    assert_eq!(p, q);
    tracer.record_event(event_a);
    let r = tracer.snapshot();
    assert!(q < r);
    assert_ne!(q, r);
    tracer.record_event(event_a);
    let s = tracer.snapshot();
    assert!(r < s);
    assert_ne!(r, s);
    tracer.record_event(event_b);
    let t = tracer.snapshot();
    assert!(s < t);
    assert_ne!(s, t);
    tracer.record_event(event_a);
    let u = tracer.snapshot();
    assert!(t < u);
    assert_ne!(t, u);
    tracer.service();
    let v = tracer.snapshot();
    // Should service calls affect the outcome of snapshot_history()?
    assert!(u < v);
    assert_ne!(u, v);
}

#[test]
fn round_trip_merge_snapshot() {
    let tracer_id_foo = TracerId(NonZeroU32::new(1).expect("Could not make tracer_id"));
    let tracer_id_bar = TracerId(NonZeroU32::new(2).expect("Could not make tracer_id"));

    let mut backend = DevNull;
    let mut tracer_foo = Tracer::initialize(tracer_id_foo, &mut backend);
    let event = EventId(NonZeroU32::new(314).expect("Should be non-zero"));
    tracer_foo.record_event(event);
    let snap_foo_a = tracer_foo.snapshot();

    // Re-initialize a tracer with no previous history
    let mut backend = DevNull;
    let mut tracer_bar = Tracer::initialize(tracer_id_bar, &mut backend);
    tracer_bar.merge_history(snap_foo_a.clone());
    let snap_bar_b = tracer_bar.snapshot();

    assert!(snap_foo_a < snap_bar_b);

    tracer_foo.record_event(event);
    let snap_foo_c = tracer_foo.snapshot();

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    tracer_bar.merge_history(snap_foo_c.clone());
    let snap_bar_d = tracer_bar.snapshot();
    assert!(snap_foo_c < snap_bar_d);

    tracer_bar.merge_history(snap_foo_c);

    assert!(
        tracer_foo.snapshot() < tracer_bar.snapshot(),
        "After merging, the bar should be just a bit ahead of foo"
    );
}
