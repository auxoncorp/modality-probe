use truce::*;

struct Buffer {
    buffer: Vec<u8>,
}
impl Buffer {
    fn new(size: usize) -> Self {
        Buffer {
            buffer: (0..size).map(|i| (i / 255) as u8).collect(),
        }
    }

    fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.buffer.as_mut_slice()
    }
}

#[test]
fn tracer_lifecycle_does_not_panic() {
    let tracer_id = TracerId::new(1).expect("Could not make tracer_id");

    let mut backend = Buffer::new(1024);
    let mut storage = [0u8; 1024];
    let tracer = Tracer::initialize_at(&mut storage, tracer_id).expect("Could not init");

    let p = tracer.share_fixed_size_history().unwrap();
    let q = tracer.share_fixed_size_history().unwrap();

    // Snapshotting moves the tracer history forward, so two consecutive snapshots
    // are not exactly the same.
    assert_ne!(p, q);
    assert_eq!(1, p.buckets_len);
    let r = tracer.share_fixed_size_history().unwrap();
    assert!(q < r);
    assert_ne!(q, r);
    let s = tracer.share_fixed_size_history().unwrap();
    assert!(r < s);
    assert_ne!(r, s);
    let t = tracer.share_fixed_size_history().unwrap();
    assert!(s < t);
    assert_ne!(s, t);
    let u = tracer.share_fixed_size_history().unwrap();
    assert!(t < u);
    assert_ne!(t, u);
    tracer
        .write_reporting(backend.as_bytes_mut())
        .expect("Could not write reporting");
    let v = tracer.share_fixed_size_history().unwrap();
    // Should write_reporting calls affect the outcome of snapshot_history()?
    assert!(u < v);
    assert_ne!(u, v);
}

#[test]
fn round_trip_merge_snapshot() {
    let tracer_id_foo = TracerId::new(1).expect("Could not make tracer_id");
    let tracer_id_bar = TracerId::new(2).expect("Could not make tracer_id");

    let mut storage_foo = [0u8; 1024];
    let tracer_foo =
        Tracer::initialize_at(&mut storage_foo, tracer_id_foo).expect("Could not init");
    let snap_foo_a = tracer_foo.share_fixed_size_history().unwrap();

    // Re-initialize a tracer with no previous history
    let mut storage_bar = [0u8; 1024];
    let tracer_bar =
        Tracer::initialize_at(&mut storage_bar, tracer_id_bar).expect("Could not init");
    assert!(tracer_bar.merge_fixed_size_history(&snap_foo_a).is_ok());
    let snap_bar_b = tracer_bar.share_fixed_size_history().unwrap();

    assert!(snap_foo_a < snap_bar_b);

    let snap_foo_c = tracer_foo.share_fixed_size_history().unwrap();

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    assert!(tracer_bar.merge_fixed_size_history(&snap_foo_c).is_ok());
    let snap_bar_d = tracer_bar.share_fixed_size_history().unwrap();
    assert!(snap_foo_c < snap_bar_d);

    assert!(tracer_bar.merge_fixed_size_history(&snap_foo_c).is_ok());

    assert!(
        &snap_foo_c < &tracer_bar.share_fixed_size_history().unwrap(),
        "After merging, the bar should be just a bit ahead of foo"
    );
}

#[test]
fn invalid_neighbor_id_in_fixed_size_merge_produces_error() {
    let tracer_id_foo = TracerId::new(1).expect("Could not make tracer_id");
    let mut storage_foo = [0u8; 1024];
    let tracer_foo =
        Tracer::initialize_at(&mut storage_foo, tracer_id_foo).expect("Could not init");

    let mut buckets = arr_macro::arr![LogicalClockBucket { id: 0, count: 0}; 256];
    buckets[0].id = 200;
    buckets[0].count = 200;
    let bad_snapshot = CausalSnapshot {
        tracer_id: 0, // An invalid value technically permissable in the C representation of this struct
        buckets,
        buckets_len: 1,
    };
    assert!(tracer_foo.merge_fixed_size_history(&bad_snapshot).is_err())
}
