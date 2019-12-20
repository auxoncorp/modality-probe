use truce::*;

#[derive(Debug)]
struct DevNull;
impl Backend for DevNull {
    fn send_tracer_data(&mut self, _data: &[u8]) -> bool {
        true
    }
}

#[test]
fn tracer_lifecycle_does_not_panic() {
    let tracer_id = TracerId::new(1).expect("Could not make tracer_id");

    let mut backend = DevNull;
    let mut storage = [0u8; 1024];
    let tracer =
        Tracer::initialize_at(&mut storage, tracer_id, &mut backend).expect("Could not init");
    let event_a = EventId::new(2).expect("Should be non-zero");
    let event_b = EventId::new(3).expect("Should be non-zero");

    let p = tracer.snapshot();
    let q = tracer.snapshot();
    assert_eq!(p, q);
    assert_eq!(0, p.buckets_len);
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
    let tracer_id_foo = TracerId::new(1).expect("Could not make tracer_id");
    let tracer_id_bar = TracerId::new(2).expect("Could not make tracer_id");

    let mut backend = DevNull;
    let mut storage_foo = [0u8; 1024];
    let tracer_foo = Tracer::initialize_at(&mut storage_foo, tracer_id_foo, &mut backend)
        .expect("Could not init");
    let event = EventId::new(314).expect("Should be non-zero");
    tracer_foo.record_event(event);
    let snap_foo_a = tracer_foo.snapshot();

    // Re-initialize a tracer with no previous history
    let mut backend = DevNull;
    let mut storage_bar = [0u8; 1024];
    let tracer_bar = Tracer::initialize_at(&mut storage_bar, tracer_id_bar, &mut backend)
        .expect("Could not init");
    tracer_bar.merge_history(&snap_foo_a);
    let snap_bar_b = tracer_bar.snapshot();

    assert!(snap_foo_a < snap_bar_b);

    tracer_foo.record_event(event);
    let snap_foo_c = tracer_foo.snapshot();

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    tracer_bar.merge_history(&snap_foo_c);
    let snap_bar_d = tracer_bar.snapshot();
    assert!(snap_foo_c < snap_bar_d);

    tracer_bar.merge_history(&snap_foo_c);

    assert!(
        tracer_foo.snapshot() < tracer_bar.snapshot(),
        "After merging, the bar should be just a bit ahead of foo"
    );
}
