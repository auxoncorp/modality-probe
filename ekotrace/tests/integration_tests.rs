use alloc_log_report::*;
use ekotrace::*;

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
    let tracer = Ekotrace::initialize_at(&mut storage, tracer_id).expect("Could not init");

    let p = tracer.distribute_fixed_size_snapshot().unwrap();
    let q = tracer.distribute_fixed_size_snapshot().unwrap();

    // Snapshotting moves the tracer history forward, so two consecutive snapshots
    // are not exactly the same.
    assert_ne!(p, q);
    assert_eq!(1, p.clocks_len);
    let r = tracer.distribute_fixed_size_snapshot().unwrap();
    assert!(q < r);
    assert_ne!(q, r);
    let s = tracer.distribute_fixed_size_snapshot().unwrap();
    assert!(r < s);
    assert_ne!(r, s);
    let t = tracer.distribute_fixed_size_snapshot().unwrap();
    assert!(s < t);
    assert_ne!(s, t);
    let u = tracer.distribute_fixed_size_snapshot().unwrap();
    assert!(t < u);
    assert_ne!(t, u);
    tracer
        .report(backend.as_bytes_mut())
        .expect("Could not write reporting");
    let v = tracer.distribute_fixed_size_snapshot().unwrap();
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
        Ekotrace::initialize_at(&mut storage_foo, tracer_id_foo).expect("Could not init");
    let snap_foo_a = tracer_foo.distribute_fixed_size_snapshot().unwrap();

    // Re-initialize a tracer with no previous history
    let mut storage_bar = [0u8; 1024];
    let tracer_bar =
        Ekotrace::initialize_at(&mut storage_bar, tracer_id_bar).expect("Could not init");
    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_a).is_ok());
    let snap_bar_b = tracer_bar.distribute_fixed_size_snapshot().unwrap();

    assert!(snap_foo_a < snap_bar_b);

    let snap_foo_c = tracer_foo.distribute_fixed_size_snapshot().unwrap();

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_c).is_ok());
    let snap_bar_d = tracer_bar.distribute_fixed_size_snapshot().unwrap();
    assert!(snap_foo_c < snap_bar_d);

    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_c).is_ok());

    assert!(
        &snap_foo_c < &tracer_bar.distribute_fixed_size_snapshot().unwrap(),
        "After merging, the bar should be just a bit ahead of foo"
    );
}

#[test]
fn invalid_neighbor_id_in_fixed_size_merge_produces_error() {
    let tracer_id_foo = TracerId::new(1).expect("Could not make tracer_id");
    let mut storage_foo = [0u8; 1024];
    let tracer_foo =
        Ekotrace::initialize_at(&mut storage_foo, tracer_id_foo).expect("Could not init");

    let mut clocks = [LogicalClock { id: 0, count: 0 }; 256];
    clocks[0].id = 200;
    clocks[0].count = 200;
    let bad_snapshot = CausalSnapshot {
        tracer_id: 0, // An invalid value technically permissable in the C representation of this struct
        clocks,
        clocks_len: 1,
    };
    assert!(tracer_foo.merge_fixed_size_snapshot(&bad_snapshot).is_err())
}

#[test]
fn happy_path_backend_service() {
    let mut storage_foo = [0u8; 1024];
    let tracer_id_foo = TracerId::new(123).expect("Could not make tracer_id");
    let mut tracer = Ekotrace::new_with_storage(&mut storage_foo, tracer_id_foo)
        .expect("Could not make new tracer");
    let mut backend = [0u8; 1024];
    let bytes_written = tracer
        .report(&mut backend)
        .expect("Could not write reporting message");
    let log_report =
        LogReport::from_lcm(&backend[..bytes_written]).expect("Could not read log report");
    assert_eq!(123, log_report.tracer_id);
    assert!(!log_report.flags.has_overflowed_log);
    assert!(!log_report.flags.has_overflowed_num_clocks);
    assert_eq!(1, log_report.segments.len());
    let segment = log_report.segments.first().expect("Should have 1 segment");
    assert!(segment.events.is_empty());
    assert_eq!(
        1,
        segment.clocks.len(),
        "only one clock of interest since nothing has been merged in"
    );
    let clock = segment
        .clocks
        .first()
        .expect("Should have 1 clock bucket for own self");
    assert_eq!(123, clock.tracer_id, "clock tracer ids should match");


    // Expect no increments; this happens after the data is serialized.
    assert_eq!(0, clock.count, "expect no clock increments");
}

#[test]
fn all_allowed_events() {
    // zero-value EventId is not allowed
    assert!(EventId::new(0).is_none());

    assert!(EventId::new(1).is_some());
    assert!(EventId::new(2).is_some());
    assert!(EventId::new(EventId::MAX_USER_ID - 1).is_some());
    assert!(EventId::new(EventId::MAX_USER_ID - 2).is_some());
    assert!(EventId::new(EventId::MAX_USER_ID).is_some());

    // Users cannot construct an internal id (one in the reserved range)
    assert!(EventId::new(EventId::MAX_USER_ID + 1).is_none());
    assert!(EventId::new(EventId::MAX_USER_ID + 2).is_none());
    assert!(EventId::new(EventId::MAX_INTERNAL_ID).is_none());
    assert_eq!(EventId::MAX_INTERNAL_ID, (core::u32::MAX / 2));
    assert_eq!(
        EventId::MAX_USER_ID,
        (core::u32::MAX / 2) - EventId::NUM_RESERVED_IDS
    );

    assert_eq!(
        0,
        EventId::MAX_INTERNAL_ID & 0b1000_0000_0000_0000_0000_0000_0000_0000
    );
    assert_eq!(
        0,
        EventId::MAX_USER_ID & 0b1000_0000_0000_0000_0000_0000_0000_0000
    );
}

#[test]
fn try_initialize_handles_raw_tracer_ids() {
    let mut storage = [0u8; 512];
    assert!(Ekotrace::try_initialize_at(&mut storage, 0).is_err());
    assert!(Ekotrace::try_initialize_at(&mut storage, TracerId::MAX_ID + 1).is_err());
    assert!(Ekotrace::try_initialize_at(&mut storage, 1).is_ok());
}

#[test]
fn try_record_event_raw_tracer_ids() {
    let mut storage = [0u8; 512];
    let tracer = Ekotrace::try_initialize_at(&mut storage, 1).unwrap();
    assert!(tracer.try_record_event(0).is_err());
    assert!(tracer.try_record_event(EventId::MAX_USER_ID + 1).is_err());
    assert!(tracer.try_record_event(1).is_ok());
}

// TODO - test overflowing num buckets
// TODO - test overflowing log

#[allow(dead_code)]
mod lcm {
    include!(concat!(env!("OUT_DIR"), "/in_system.rs"));
}
