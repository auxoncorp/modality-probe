#![deny(warnings)]

use core::mem;
use core::num::NonZeroU16;
use modality_probe::*;
use proptest::prelude::*;
use std::{
    convert::{TryFrom, TryInto},
    process::{Command, Stdio},
};

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
    let probe = ModalityProbe::initialize_at(
        &mut storage,
        probe_id,
        RestartCounterProvider::NoRestartTracking,
    )?;

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
    let probe_foo = ModalityProbe::initialize_at(
        &mut storage_foo,
        probe_id_foo,
        RestartCounterProvider::NoRestartTracking,
    )?;
    let snap_foo_a = probe_foo.produce_snapshot()?;

    // Re-initialize a probe with no previous history
    let mut storage_bar = [0u8; 1024];
    let probe_bar = ModalityProbe::initialize_at(
        &mut storage_bar,
        probe_id_bar,
        RestartCounterProvider::NoRestartTracking,
    )?;
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
    let mut probe = ModalityProbe::new_with_storage(
        &mut storage_foo,
        probe_id_foo,
        RestartCounterProvider::NoRestartTracking,
    )?;
    let mut backend = [0u8; 1024];

    probe.record_event(EventId::new(1).unwrap());
    let bytes_written = probe.report(&mut backend)?.unwrap();
    let log_report = wire::WireReport::new(&backend[..bytes_written.get()])
        .expect("Could not read from bulk report format bytes");
    assert_eq!(Ok(ProbeId::try_from(123).unwrap()), log_report.probe_id());
    assert_eq!(log_report.seq_num(), 0);

    assert_eq!(
        log_report.n_clocks(),
        1,
        "Should have 1 clock bucket for own self"
    );

    // When a probe inits, it also logs an internal event
    assert_eq!(log_report.n_log_entries(), 2);

    let payload_len = log_report.payload_len();
    let payload = &log_report.payload()[..payload_len];
    assert_eq!(
        payload_len,
        core::mem::size_of::<LogicalClock>() + (2 * core::mem::size_of::<log::LogEntry>())
    );
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
    probe.record_event(EventId::new(2).unwrap());
    let bytes_written = probe.report(&mut backend)?.unwrap();
    let log_report = wire::WireReport::new(&backend[..bytes_written.get()]).unwrap();
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
    assert!(ModalityProbe::try_initialize_at(
        &mut storage,
        0,
        RestartCounterProvider::NoRestartTracking
    )
    .is_err());
    assert!(ModalityProbe::try_initialize_at(
        &mut storage,
        ProbeId::MAX_ID + 1,
        RestartCounterProvider::NoRestartTracking
    )
    .is_err());
    assert!(ModalityProbe::try_initialize_at(
        &mut storage,
        1,
        RestartCounterProvider::NoRestartTracking
    )
    .is_ok());
}

#[test]
fn try_record_event_raw_probe_ids() -> Result<(), ModalityProbeError> {
    let mut storage = [0u8; 512];
    let probe = ModalityProbe::try_initialize_at(
        &mut storage,
        1,
        RestartCounterProvider::NoRestartTracking,
    )?;
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
    let probe = ModalityProbe::try_initialize_at(
        &mut storage,
        1,
        RestartCounterProvider::NoRestartTracking,
    )?;
    assert!(probe.try_record_event(0).is_err());
    assert!(probe.try_record_event(EventId::MAX_USER_ID).is_ok());

    // Only room for a header, hard error since we can't log a single event
    let mut report_dest =
        vec![0u8; wire::WireReport::<&[u8]>::header_len() + mem::size_of::<log::LogEntry>() - 1];
    assert_eq!(
        probe.report(&mut report_dest),
        Err(ReportError::InsufficientDestinationSize)
    );

    // Not enough room for the frontier clocks, only a single event
    let mut report_dest =
        vec![0u8; wire::WireReport::<&[u8]>::header_len() + mem::size_of::<log::LogEntry>()];
    let bytes_written = probe.report(&mut report_dest)?.unwrap();
    let log_report = wire::WireReport::new(&report_dest[..bytes_written.get()]).unwrap();

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

#[test]
fn report_missed_log_items() -> Result<(), ModalityProbeError> {
    const NUM_STORAGE_BYTES: usize = 512;
    let mut storage = [0u8; NUM_STORAGE_BYTES];
    let probe = ModalityProbe::try_initialize_at(
        &mut storage,
        1,
        RestartCounterProvider::NoRestartTracking,
    )?;
    let event = EventId::new(2).unwrap();

    // Should be repeatable, counts are cleared on each report
    for _ in 0..3 {
        for _ in 0..NUM_STORAGE_BYTES * 2 {
            probe.record_event(event);
        }

        let mut report_dest = [0u8; 1024];
        let bytes_written = probe.report(&mut report_dest)?.unwrap();
        let log_report = wire::WireReport::new(&report_dest[..bytes_written.get()]).unwrap();

        assert_eq!(log_report.n_clocks(), 1);
        assert_eq!(log_report.n_log_entries(), 86);

        let offset = log_report.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let log_bytes = &log_report.payload()[offset..];

        // First event with payload should indicate how many missed items
        let raw_event =
            u32::from_le_bytes([log_bytes[0], log_bytes[1], log_bytes[2], log_bytes[3]]);
        let raw_payload =
            u32::from_le_bytes([log_bytes[4], log_bytes[5], log_bytes[6], log_bytes[7]]);
        let log_event = unsafe { log::LogEntry::new_unchecked(raw_event) };
        assert_eq!(
            log_event.interpret_as_event_id().unwrap(),
            EventId::EVENT_LOG_ITEMS_MISSED
        );

        assert_eq!(raw_payload, 941);
    }

    Ok(())
}

#[test]
fn export_cli_produces_a_reasonable_dot_file() {
    let run = |args: &[&str]| {
        let mut out = Command::new("./target/debug/modality-probe")
            .args(args)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        assert!(out.wait().unwrap().success());

        let dot = Command::new("dot")
            .stdin(out.stdout.unwrap())
            .args(&["-T", "svg"])
            .output()
            .unwrap();
        assert!(dot.status.success(), "{:#?}", dot)
    };
    run(&[
        "export",
        "acyclic",
        "-c",
        "./tests/fixtures/test-component",
        "-r",
        "./tests/fixtures/test-log.jsonl",
    ]);
    run(&[
        "export",
        "cyclic",
        "-c",
        "./tests/fixtures/test-component",
        "-r",
        "./tests/fixtures/test-log.jsonl",
    ]);
    run(&[
        "export",
        "acyclic",
        "--interactions-only",
        "-c",
        "./tests/fixtures/test-component",
        "-r",
        "./tests/fixtures/test-log.jsonl",
    ]);
    run(&[
        "export",
        "cyclic",
        "--interactions-only",
        "-c",
        "./tests/fixtures/test-component",
        "-r",
        "./tests/fixtures/test-log.jsonl",
    ]);
}

proptest! {
    #[test]
    fn reports_never_end_between_multi_log_items(
        num_events in 1_usize..256_usize,
        num_events_with_payload in 1_usize..256_usize,
        report_buffer_space in 0_usize..256_usize,
        event_payload in proptest::num::u32::ANY,
    ) {
        // num_events and num_events_with_payload set to at least 1
        // so that we can have a total of at least 2 events

        let mut storage = [0u8; 512];
        let probe = ModalityProbe::try_initialize_at(
            &mut storage,
            1,
            RestartCounterProvider::NoRestartTracking).unwrap();
        let event_a = EventId::new(2).unwrap();
        let event_b = EventId::new(3).unwrap();

        for _ in 0..num_events {
            probe.record_event(event_a);
        }
        for _ in 0..num_events_with_payload {
            probe.record_event_with_payload(event_b, event_payload);
        }

        let min_report_size =
            wire::WireReport::<&[u8]>::header_len() + (3 * mem::size_of::<LogicalClock>());
        let mut report_dest = vec![0u8; min_report_size + report_buffer_space];

        let bytes_written = probe.report(&mut report_dest).unwrap().unwrap();
        let log_report = wire::WireReport::new(&report_dest[..bytes_written.get()]).unwrap();

        // Should have some clocks, and at least two entries
        prop_assert!(log_report.n_clocks() > 0);
        prop_assert!(log_report.n_log_entries() >= 2);

        let offset = log_report.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let log_bytes = &log_report.payload()[offset..];
        assert_eq!(log_bytes.len() % mem::size_of::<log::LogEntry>(), 0);

        let tail_index = log_report.n_log_entries() as usize * mem::size_of::<log::LogEntry>();
        let last_item = u32::from_le_bytes([
            log_bytes[tail_index - 4],
            log_bytes[tail_index - 3],
            log_bytes[tail_index - 2],
            log_bytes[tail_index - 1],
        ]);
        let last_item = unsafe { log::LogEntry::new_unchecked(last_item) };

        let tail_index = tail_index - mem::size_of::<log::LogEntry>();
        let second_to_last_item = u32::from_le_bytes([
            log_bytes[tail_index - 4],
            log_bytes[tail_index - 3],
            log_bytes[tail_index - 2],
            log_bytes[tail_index - 1],
        ]);
        let second_to_last_item = unsafe { log::LogEntry::new_unchecked(second_to_last_item) };

        // If the second-to-last item is not a two-item log entry
        if !second_to_last_item.has_clock_bit_set()
            && !second_to_last_item.has_event_with_payload_bit_set() {
            // Then the last item also must not be the start of a multi-item entry
            prop_assert!(
                !last_item.has_clock_bit_set(),
                "Last item has clock bit set: 0x{:X}",
                last_item.raw()
            );
            prop_assert!(
                !last_item.has_event_with_payload_bit_set(),
                "Last item has event with payload bit set: 0x{:X}",
                last_item.raw()
            );
        }
        // else the second-to-last item is a two-item log entry,
        // and therefor the last item can be anything (event payload, or clock)
    }
}

#[test]
fn persistent_restart_sequence_id() -> Result<(), ModalityProbeError> {
    let mut next_id_provider = PersistentRestartProvider {
        next_seq_id: NonZeroU16::new(100).unwrap(),
        count: 0,
    };

    // When a probe is tracking restarts, then it gets the initial epoch portion
    // of the clock from the implementation
    {
        let provider = RestartCounterProvider::Rust(RustRestartCounterProvider {
            iface: &mut next_id_provider,
        });

        let probe_id = 1u32.try_into()?;
        let mut storage = [0u8; 1024];
        let probe = ModalityProbe::initialize_at(&mut storage, probe_id, provider)?;

        let now = probe.now();
        assert_eq!(now.clock.epoch.0, 100);
        assert_eq!(now.clock.ticks.0, 0);

        let mut report_dest = [0u8; 512];
        let bytes_written = probe.report(&mut report_dest)?.unwrap();
        let log_report = wire::WireReport::new(&report_dest[..bytes_written.get()]).unwrap();
        assert_eq!(log_report.persistent_epoch_counting(), true);
    }
    assert_eq!(next_id_provider.next_seq_id.get(), 101);
    assert_eq!(next_id_provider.count, 1);

    {
        let provider = RestartCounterProvider::Rust(RustRestartCounterProvider {
            iface: &mut next_id_provider,
        });

        let probe_id = 1u32.try_into()?;
        let mut storage = [0u8; 1024];
        let probe = ModalityProbe::initialize_at(&mut storage, probe_id, provider)?;

        let now = probe.now();
        assert_eq!(now.clock.epoch.0, 101);
        assert_eq!(now.clock.ticks.0, 0);

        let mut report_dest = [0u8; 512];
        let bytes_written = probe.report(&mut report_dest)?.unwrap();
        let log_report = wire::WireReport::new(&report_dest[..bytes_written.get()]).unwrap();
        assert_eq!(log_report.persistent_epoch_counting(), true);
    }
    assert_eq!(next_id_provider.next_seq_id.get(), 102);
    assert_eq!(next_id_provider.count, 2);

    Ok(())
}

struct PersistentRestartProvider {
    next_seq_id: NonZeroU16,
    count: usize,
}

impl RestartCounter for PersistentRestartProvider {
    fn next_sequence_id(&mut self, _probe_id: ProbeId) -> Option<NonZeroU16> {
        let next = self.next_seq_id;
        self.next_seq_id = NonZeroU16::new(next.get() + 1).unwrap();
        self.count += 1;
        Some(next)
    }
}
