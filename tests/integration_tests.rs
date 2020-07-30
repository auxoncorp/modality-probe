#![deny(warnings)]

use core::mem;
use modality_probe::*;
use std::convert::{TryFrom, TryInto};

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
fn probe_lifecycle_does_not_panic() -> Result<(), ModalityProbeError> {
    let probe_id = 1u32.try_into()?;

    let mut backend = Buffer::new(1024);
    let mut storage = [0u8; 1024];
    let probe = ModalityProbe::initialize_at(&mut storage, probe_id)?;

    let p = probe.produce_snapshot()?;
    let q = probe.produce_snapshot()?;

    // Snapshotting moves the probe history forward, so two consecutive snapshots
    // are not exactly the same.
    assert_ne!(p, q);
    let r = probe.produce_snapshot()?;
    assert!(q < r);
    assert_ne!(q, r);
    let s = probe.produce_snapshot()?;
    assert!(r < s);
    assert_ne!(r, s);
    let t = probe.produce_snapshot()?;
    assert!(s < t);
    assert_ne!(s, t);
    let u = probe.produce_snapshot()?;
    assert!(t < u);
    assert_ne!(t, u);
    probe.report(backend.as_bytes_mut())?;
    let v = probe.produce_snapshot()?;
    // Should write_reporting calls affect the outcome of snapshot_history()?
    assert!(u < v);
    assert_ne!(u, v);
    Ok(())
}

#[test]
fn round_trip_merge_snapshot() -> Result<(), ModalityProbeError> {
    let probe_id_foo = 1.try_into()?;
    let probe_id_bar = 2.try_into()?;

    let mut storage_foo = [0u8; 1024];
    let probe_foo = ModalityProbe::initialize_at(&mut storage_foo, probe_id_foo)?;
    let snap_foo_a = probe_foo.produce_snapshot()?;

    // Re-initialize a probe with no previous history
    let mut storage_bar = [0u8; 1024];
    let probe_bar = ModalityProbe::initialize_at(&mut storage_bar, probe_id_bar)?;
    assert!(probe_bar.merge_snapshot(&snap_foo_a).is_ok());
    let snap_bar_b = probe_bar.produce_snapshot()?;

    let snap_foo_c = probe_foo.produce_snapshot()?;

    assert!(snap_foo_a < snap_foo_c);
    assert_eq!(None, snap_bar_b.partial_cmp(&snap_foo_c));

    assert!(probe_bar.merge_snapshot(&snap_foo_c).is_ok());
    let _snap_bar_d = probe_bar.produce_snapshot()?;

    assert!(probe_bar.merge_snapshot(&snap_foo_c).is_ok());

    Ok(())
}

#[test]
fn happy_path_backend_service() -> Result<(), ModalityProbeError> {
    let mut storage_foo = [0u8; 1024];
    let probe_id_foo = 123.try_into()?;
    let mut probe = ModalityProbe::new_with_storage(&mut storage_foo, probe_id_foo)?;
    let mut backend = [0u8; 1024];
    let bytes_written = probe.report(&mut backend)?;
    let log_report = wire::WireReport::new(&backend[..bytes_written])
        .expect("Could not read from bulk report format bytes");
    assert_eq!(Ok(ProbeId::try_from(123).unwrap()), log_report.probe_id());
    assert_eq!(log_report.seq_num(), 0);

    assert_eq!(
        log_report.n_clocks(),
        1,
        "Should have 1 clock bucket for own self"
    );
    assert_eq!(log_report.n_log_entries(), 0);

    let payload_len = log_report.payload_len();
    let payload = &log_report.payload()[..payload_len];
    assert_eq!(payload_len, core::mem::size_of::<LogicalClock>());
    let item = unsafe {
        log::LogEntry::new_unchecked(u32::from_le_bytes([
            payload[0], payload[1], payload[2], payload[3],
        ]))
    };
    assert_eq!(
        item.interpret_as_logical_clock_probe_id(),
        probe_id_foo.get_raw(),
        "clock probe ids should match"
    );

    // Expect no increments; this happens after the data is serialized.
    assert_eq!(log_report.clock(), 0);

    // Another report should bump the sequence number
    let bytes_written = probe.report(&mut backend)?;
    let log_report = wire::WireReport::new(&backend[..bytes_written]).unwrap();
    assert_eq!(Ok(ProbeId::try_from(123).unwrap()), log_report.probe_id());
    assert_eq!(log_report.seq_num(), 1);

    Ok(())
}

#[test]
fn all_allowed_events() -> Result<(), ModalityProbeError> {
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
fn try_initialize_handles_raw_probe_ids() {
    let mut storage = [0u8; 512];
    assert!(ModalityProbe::try_initialize_at(&mut storage, 0).is_err());
    assert!(ModalityProbe::try_initialize_at(&mut storage, ProbeId::MAX_ID + 1).is_err());
    assert!(ModalityProbe::try_initialize_at(&mut storage, 1).is_ok());
}

#[test]
fn try_record_event_raw_probe_ids() -> Result<(), ModalityProbeError> {
    let mut storage = [0u8; 512];
    let probe = ModalityProbe::try_initialize_at(&mut storage, 1)?;
    assert!(probe.try_record_event(0).is_err());
    assert!(probe.try_record_event(EventId::MAX_USER_ID).is_ok());
    // Allowed to record internal events
    assert!(probe.try_record_event(EventId::MAX_INTERNAL_ID).is_ok());
    // Still can't exceed the valid range
    assert!(probe
        .try_record_event(EventId::MAX_INTERNAL_ID + 1)
        .is_err());
    assert!(probe.try_record_event(1).is_ok());
    Ok(())
}

#[test]
fn report_buffer_too_small_error() -> Result<(), ModalityProbeError> {
    let mut storage = [0u8; 512];
    let probe = ModalityProbe::try_initialize_at(&mut storage, 1)?;
    assert!(probe.try_record_event(0).is_err());
    assert!(probe.try_record_event(EventId::MAX_USER_ID).is_ok());

    // Only room for a header, hard error since we can't log a single event
    let mut report_dest = [0u8; 20 + mem::size_of::<log::LogEntry>() - 1];
    assert_eq!(
        report_dest.len(),
        wire::WireReport::<&[u8]>::header_len() + mem::size_of::<log::LogEntry>() - 1
    );
    assert_eq!(
        probe.report(&mut report_dest),
        Err(ReportError::InsufficientDestinationSize)
    );

    // Not enough room for the frontier clocks, only a single event
    let mut report_dest = [0u8; 20 + mem::size_of::<log::LogEntry>()];
    let bytes_written = probe.report(&mut report_dest)?;
    let log_report = wire::WireReport::new(&report_dest[..bytes_written]).unwrap();

    // Only a single internal event is logged
    assert_eq!(log_report.n_clocks(), 0);
    assert_eq!(log_report.n_log_entries(), 1);
    assert_eq!(log_report.payload_len(), mem::size_of::<log::LogEntry>());
    let payload = log_report.payload();
    let raw_event = u32::from_le_bytes([payload[0], payload[1], payload[2], payload[3]]);
    assert_eq!(
        raw_event,
        EventId::EVENT_INSUFFICIENT_REPORT_BUFFER_SIZE.get_raw()
    );

    Ok(())
}

// TODO - test overflowing num buckets
// TODO - test overflowing log
