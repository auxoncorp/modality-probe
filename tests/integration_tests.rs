use ekotrace::*;
use std::convert::{TryFrom, TryInto};
use util::alloc_log_report::*;

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
fn tracer_lifecycle_does_not_panic() -> Result<(), EkotraceError> {
    let tracer_id = 1u32.try_into()?;

    let mut backend = Buffer::new(1024);
    let mut storage = [0u8; 1024];
    let tracer = Ekotrace::initialize_at(&mut storage, tracer_id)?;

    let p = tracer.distribute_fixed_size_snapshot()?;
    let q = tracer.distribute_fixed_size_snapshot()?;

    // Snapshotting moves the tracer history forward, so two consecutive snapshots
    // are not exactly the same.
    assert_ne!(p, q);
    assert_eq!(1, p.clocks_len);
    let r = tracer.distribute_fixed_size_snapshot()?;
    assert!(q < r);
    assert_ne!(q, r);
    let s = tracer.distribute_fixed_size_snapshot()?;
    assert!(r < s);
    assert_ne!(r, s);
    let t = tracer.distribute_fixed_size_snapshot()?;
    assert!(s < t);
    assert_ne!(s, t);
    let u = tracer.distribute_fixed_size_snapshot()?;
    assert!(t < u);
    assert_ne!(t, u);
    tracer.report(backend.as_bytes_mut())?;
    let v = tracer.distribute_fixed_size_snapshot()?;
    // Should write_reporting calls affect the outcome of snapshot_history()?
    assert!(u < v);
    assert_ne!(u, v);
    Ok(())
}

#[test]
fn round_trip_merge_snapshot() -> Result<(), EkotraceError> {
    let tracer_id_foo = 1.try_into()?;
    let tracer_id_bar = 2.try_into()?;

    let mut storage_foo = [0u8; 1024];
    let tracer_foo = Ekotrace::initialize_at(&mut storage_foo, tracer_id_foo)?;
    let snap_foo_a = tracer_foo.distribute_fixed_size_snapshot()?;

    // Re-initialize a tracer with no previous history
    let mut storage_bar = [0u8; 1024];
    let tracer_bar = Ekotrace::initialize_at(&mut storage_bar, tracer_id_bar)?;
    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_a).is_ok());
    let snap_bar_b = tracer_bar.distribute_fixed_size_snapshot()?;

    assert!(snap_foo_a < snap_bar_b);

    let snap_foo_c = tracer_foo.distribute_fixed_size_snapshot()?;

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_c).is_ok());
    let snap_bar_d = tracer_bar.distribute_fixed_size_snapshot()?;
    assert!(snap_foo_c < snap_bar_d);

    assert!(tracer_bar.merge_fixed_size_snapshot(&snap_foo_c).is_ok());

    assert!(
        &snap_foo_c < &tracer_bar.distribute_fixed_size_snapshot()?,
        "After merging, the bar should be just a bit ahead of foo"
    );
    Ok(())
}

#[test]
fn invalid_neighbor_id_in_fixed_size_merge_produces_error() -> Result<(), EkotraceError> {
    let tracer_id_foo = 1.try_into()?;
    let mut storage_foo = [0u8; 1024];
    let tracer_foo = Ekotrace::initialize_at(&mut storage_foo, tracer_id_foo)?;

    let mut clocks = [LogicalClock {
        id: TracerId::new(TracerId::MAX_ID).unwrap(),
        count: 0,
    }; 256];
    clocks[0].id = 200.try_into().unwrap();
    clocks[0].count = 200;
    let bad_snapshot = CausalSnapshot {
        tracer_id: 0, // An invalid value technically permissable in the C representation of this struct
        clocks,
        clocks_len: 1,
    };
    assert!(tracer_foo.merge_fixed_size_snapshot(&bad_snapshot).is_err());
    Ok(())
}

#[test]
fn happy_path_backend_service() -> Result<(), EkotraceError> {
    let mut storage_foo = [0u8; 1024];
    let tracer_id_foo = 123.try_into()?;
    let mut tracer = Ekotrace::new_with_storage(&mut storage_foo, tracer_id_foo)?;
    let mut backend = [0u8; 1024];
    let bytes_written = tracer.report(&mut backend)?;
    let log_report = LogReport::try_from_bulk_bytes(&backend[..bytes_written])
        .expect("Could not read from bulk report format bytes");
    assert_eq!(TracerId::try_from(123).unwrap(), log_report.tracer_id);
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
    assert_eq!(123, clock.id.get_raw(), "clock tracer ids should match");

    // Expect no increments; this happens after the data is serialized.
    assert_eq!(0, clock.count, "expect no clock increments");
    Ok(())
}

#[test]
fn all_allowed_events() -> Result<(), EkotraceError> {
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
    assert_eq!(EventId::MAX_INTERNAL_ID, (core::u32::MAX / 4));
    assert_eq!(
        EventId::MAX_USER_ID,
        (core::u32::MAX / 4) - EventId::NUM_RESERVED_IDS
    );

    assert_eq!(
        0,
        EventId::MAX_INTERNAL_ID & 0b1000_0000_0000_0000_0000_0000_0000_0000
    );
    assert_eq!(
        0,
        EventId::MAX_USER_ID & 0b1000_0000_0000_0000_0000_0000_0000_0000
    );
    Ok(())
}

#[test]
fn try_initialize_handles_raw_tracer_ids() {
    let mut storage = [0u8; 512];
    assert!(Ekotrace::try_initialize_at(&mut storage, 0).is_err());
    assert!(Ekotrace::try_initialize_at(&mut storage, TracerId::MAX_ID + 1).is_err());
    assert!(Ekotrace::try_initialize_at(&mut storage, 1).is_ok());
}

#[test]
fn try_record_event_raw_tracer_ids() -> Result<(), EkotraceError> {
    let mut storage = [0u8; 512];
    let tracer = Ekotrace::try_initialize_at(&mut storage, 1)?;
    assert!(tracer.try_record_event(0).is_err());
    assert!(tracer.try_record_event(EventId::MAX_USER_ID).is_ok());
    // Allowed to record internal events
    assert!(tracer.try_record_event(EventId::MAX_INTERNAL_ID).is_ok());
    // Still can't exceed the valid range
    assert!(tracer
        .try_record_event(EventId::MAX_INTERNAL_ID + 1)
        .is_err());
    assert!(tracer.try_record_event(1).is_ok());
    Ok(())
}

#[test]
fn snapshot_extension_data_smuggling() -> Result<(), EkotraceError> {
    let mut storage_foo = [0u8; 1024];
    let tracer_id_foo = 123.try_into()?;
    let mut foo = Ekotrace::new_with_storage(&mut storage_foo, tracer_id_foo)?;

    let mut storage_bar = [0u8; 1024];
    let tracer_id_bar = 456.try_into()?;
    let mut bar = Ekotrace::new_with_storage(&mut storage_bar, tracer_id_bar)?;

    let mut snapshot_buffer = [0u8; 512];
    let extension = [3u8, 1, 4, 1, 5, 9];

    let bytes_written =
        foo.distribute_snapshot_with_metadata(&mut snapshot_buffer, ExtensionBytes(&extension))?;

    let found_ext = bar.merge_snapshot_with_metadata(&snapshot_buffer[..bytes_written])?;
    assert_eq!([3u8, 1, 4, 1, 5, 9], found_ext.0);
    Ok(())
}

// TODO - test overflowing num buckets
// TODO - test overflowing log
