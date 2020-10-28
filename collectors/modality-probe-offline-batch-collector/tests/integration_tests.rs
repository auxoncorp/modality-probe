#![deny(warnings)]

use modality_probe::*;
use modality_probe_collector_common::SessionId;
use modality_probe_offline_batch_collector::{OfflineBatchCollector, ProbeReportMetrics};
use proptest::prelude::*;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::mem::MaybeUninit;

const STORAGE_SIZE: usize = 512;

fn init_logging() {
    let _ = env_logger::builder().is_test(true).try_init();
}

fn fill_probe_log(probe: &mut ModalityProbe<'_>) {
    for i in 0..STORAGE_SIZE / 32 {
        probe.record_event(1.try_into().unwrap());
        probe.record_event_with_payload(2.try_into().unwrap(), i as _);
    }
}

fn write_report<W: Write>(probe: &mut ModalityProbe<'_>, out: &mut W) -> usize {
    let mut buffer = vec![0_u8; 2 * STORAGE_SIZE];
    let n_report_bytes = probe
        .report(&mut buffer[..])
        .expect("Could not produce a report");
    if let Some(nonzero_report_size) = n_report_bytes {
        out.write_all(&buffer[..nonzero_report_size.get()])
            .expect("Could not write_all");
        out.flush().unwrap();
        nonzero_report_size.get()
    } else {
        0
    }
}

fn write_corrupted_report<W: Write>(probe: &mut ModalityProbe<'_>, out: &mut W) -> usize {
    let mut buffer = vec![0_u8; 2 * STORAGE_SIZE];
    let n_report_bytes = probe
        .report(&mut buffer[..])
        .expect("Could not produce a report");
    if let Some(nonzero_report_size) = n_report_bytes {
        {
            let mut r = wire::WireReport::new(&mut buffer[..nonzero_report_size.get()]).unwrap();
            let payload = r.payload_mut();
            assert!(payload.len() > 24);
            for b in &mut payload[..24] {
                *b = 0xFF;
            }
        }
        out.write_all(&buffer[..nonzero_report_size.get()])
            .expect("Could not write_all");
        out.flush().unwrap();
        nonzero_report_size.get()
    } else {
        0
    }
}

fn write_junk_bytes<W: Write>(num_bytes: usize, out: &mut W) -> usize {
    if num_bytes != 0 {
        let junk: Vec<u8> = (0..num_bytes).map(|b| (b ^ 0x55) as u8).collect();
        assert_eq!(junk.len(), num_bytes);
        out.write_all(&junk).unwrap();
        out.flush().unwrap();
    }
    num_bytes
}

proptest! {
    #[test]
    fn interleaved_probe_reports_with_junk(
        num_reports_per_probe in 1_u64..20_u64,
        num_junk_bytes_before_reporting in 0_usize..=55_usize,
        num_junk_bytes_inbetween_reporting in 0_usize..=55_usize,
        num_junk_bytes_after_reporting in 0_usize..=55_usize,
    ) {
        const NUM_PROBES: usize = 3;

        init_logging();

        let probe_id_a = 1.try_into().unwrap();
        let mut storage_a = vec![MaybeUninit::new(0_u8); STORAGE_SIZE];
        let probe_a = ModalityProbe::initialize_at(
            &mut storage_a,
            probe_id_a,
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        let probe_id_b = 2.try_into().unwrap();
        let mut storage_b = vec![MaybeUninit::new(0_u8); STORAGE_SIZE];
        let probe_b = ModalityProbe::initialize_at(
            &mut storage_b,
            probe_id_b,
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        let probe_id_c = 3.try_into().unwrap();
        let mut storage_c = vec![MaybeUninit::new(0_u8); STORAGE_SIZE];
        let probe_c = ModalityProbe::initialize_at(
            &mut storage_c,
            probe_id_c,
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        let root_dir = tempfile::tempdir().unwrap();
        let root_path = root_dir.path().to_owned();
        let interleaved_reports_path = root_path.join("reports.bin");
        let logs_out_path = root_path.join("reports.jsonl");

        let bytes_written = {
            let mut report_file = File::create(&interleaved_reports_path).unwrap();
            let mut bytes_written = 0;

            bytes_written += write_junk_bytes(num_junk_bytes_before_reporting, &mut report_file);

            for _ in 0..num_reports_per_probe {
                fill_probe_log(probe_a);
                bytes_written += write_report(probe_a, &mut report_file);
                bytes_written += write_junk_bytes(num_junk_bytes_inbetween_reporting, &mut report_file);

                fill_probe_log(probe_b);
                bytes_written += write_report(probe_b, &mut report_file);
                bytes_written += write_junk_bytes(num_junk_bytes_inbetween_reporting, &mut report_file);

                fill_probe_log(probe_c);
                bytes_written += write_report(probe_c, &mut report_file);
                bytes_written += write_junk_bytes(num_junk_bytes_inbetween_reporting, &mut report_file);
            }

            bytes_written += write_junk_bytes(num_junk_bytes_after_reporting, &mut report_file);

            report_file.sync_all().unwrap();

            bytes_written
        };


        let metrics = {
            let mut reader = File::open(&interleaved_reports_path).unwrap();
            let mut logs_out_file = File::create(&logs_out_path).unwrap();

            let session_id = SessionId(0);
            let collector = OfflineBatchCollector::new(session_id, &mut reader, &mut logs_out_file);
            let metrics = collector.run().unwrap();

            logs_out_file.sync_all().unwrap();

            metrics
        };

        prop_assert_eq!(metrics.probe_report_metrics.len(), NUM_PROBES);
        prop_assert!(metrics.probe_report_metrics.contains_key(&probe_id_a));
        prop_assert!(metrics.probe_report_metrics.contains_key(&probe_id_b));
        prop_assert!(metrics.probe_report_metrics.contains_key(&probe_id_c));

        prop_assert_eq!(
            metrics.probe_report_metrics.get(&probe_id_a).unwrap().clone(),
            ProbeReportMetrics {
                num_reports: num_reports_per_probe as u64,
                missed_seq_nums: 0,
                last_seq_num: (num_reports_per_probe - 1).into(),
            }
        );
        prop_assert_eq!(
            metrics.probe_report_metrics.get(&probe_id_b).unwrap().clone(),
            ProbeReportMetrics {
                num_reports: num_reports_per_probe,
                missed_seq_nums: 0,
                last_seq_num: (num_reports_per_probe - 1).into(),
            }
        );
        prop_assert_eq!(
            metrics.probe_report_metrics.get(&probe_id_c).unwrap().clone(),
            ProbeReportMetrics {
                num_reports: num_reports_per_probe,
                missed_seq_nums: 0,
                last_seq_num: (num_reports_per_probe - 1).into(),
            }
        );

        prop_assert_eq!(metrics.bytes_accumulated, bytes_written as u64);
        prop_assert_eq!(
            metrics.bytes_discarded,
            (num_junk_bytes_before_reporting
                + num_junk_bytes_after_reporting
                + (num_reports_per_probe as usize) * NUM_PROBES * num_junk_bytes_inbetween_reporting)
                as u64
        );
        prop_assert_eq!(metrics.reports_discarded, 0);
    }
}

#[test]
fn missed_reports_are_detected() {
    init_logging();

    let probe_id = 1.try_into().unwrap();
    let mut storage = vec![MaybeUninit::new(0u8); STORAGE_SIZE];
    let probe = ModalityProbe::initialize_at(
        &mut storage,
        probe_id,
        RestartCounterProvider::NoRestartTracking,
    )
    .unwrap();

    let root_dir = tempfile::tempdir().unwrap();
    let root_path = root_dir.path().to_owned();
    let reports_in_path = root_path.join("reports.bin");
    let logs_out_path = root_path.join("reports.jsonl");

    let bytes_written = {
        let mut report_file = File::create(&reports_in_path).unwrap();
        let mut bytes_written = 0;

        // First report is written
        fill_probe_log(probe);
        bytes_written += write_report(probe, &mut report_file);

        // Second is thrown away
        fill_probe_log(probe);
        let mut garbage_bin = vec![0_u8; 2 * STORAGE_SIZE];
        let _ = write_report(probe, &mut garbage_bin);

        // Third report is written
        fill_probe_log(probe);
        bytes_written += write_report(probe, &mut report_file);

        report_file.sync_all().unwrap();

        bytes_written
    };

    let metrics = {
        let mut reader = File::open(&reports_in_path).unwrap();
        let mut logs_out_file = File::create(&logs_out_path).unwrap();

        let session_id = SessionId(0);
        let collector = OfflineBatchCollector::new(session_id, &mut reader, &mut logs_out_file);
        let metrics = collector.run().unwrap();

        logs_out_file.sync_all().unwrap();

        metrics
    };

    assert_eq!(metrics.probe_report_metrics.len(), 1);
    assert!(metrics.probe_report_metrics.contains_key(&probe_id));

    assert_eq!(
        metrics.probe_report_metrics.get(&probe_id).unwrap().clone(),
        ProbeReportMetrics {
            num_reports: 2,
            missed_seq_nums: 1,
            last_seq_num: 2.into(),
        }
    );

    assert_eq!(metrics.bytes_accumulated, bytes_written as u64);
    assert_eq!(metrics.bytes_discarded, 0);
    assert_eq!(metrics.reports_discarded, 0);
}

#[test]
fn discarded_reports_are_detected() {
    init_logging();

    let probe_id = 1.try_into().unwrap();
    let mut storage = vec![MaybeUninit::new(0_u8); STORAGE_SIZE];
    let probe = ModalityProbe::initialize_at(
        &mut storage,
        probe_id,
        RestartCounterProvider::NoRestartTracking,
    )
    .unwrap();

    let root_dir = tempfile::tempdir().unwrap();
    let root_path = root_dir.path().to_owned();
    let reports_in_path = root_path.join("reports.bin");
    let logs_out_path = root_path.join("reports.jsonl");

    let (bytes_written, corrupted_bytes) = {
        let mut report_file = File::create(&reports_in_path).unwrap();
        let mut bytes_written = 0;

        // First report is ok
        fill_probe_log(probe);
        bytes_written += write_report(probe, &mut report_file);

        // Second is corrupted
        fill_probe_log(probe);
        let corrupted_bytes = write_corrupted_report(probe, &mut report_file);
        bytes_written += corrupted_bytes;

        report_file.sync_all().unwrap();

        (bytes_written, corrupted_bytes)
    };

    let metrics = {
        let mut reader = File::open(&reports_in_path).unwrap();
        let mut logs_out_file = File::create(&logs_out_path).unwrap();

        let session_id = SessionId(0);
        let collector = OfflineBatchCollector::new(session_id, &mut reader, &mut logs_out_file);
        let metrics = collector.run().unwrap();

        logs_out_file.sync_all().unwrap();

        metrics
    };

    assert_eq!(metrics.probe_report_metrics.len(), 1);
    assert!(metrics.probe_report_metrics.contains_key(&probe_id));

    assert_eq!(
        metrics.probe_report_metrics.get(&probe_id).unwrap().clone(),
        ProbeReportMetrics {
            num_reports: 1,
            missed_seq_nums: 0,
            last_seq_num: 0.into(),
        }
    );

    assert_eq!(metrics.bytes_accumulated, bytes_written as u64);
    assert_eq!(metrics.bytes_discarded, corrupted_bytes as u64);
    assert_eq!(metrics.reports_discarded, 1);
}
