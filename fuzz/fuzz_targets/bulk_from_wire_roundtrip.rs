#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    match modality_probe::report::bulk::try_bulk_from_wire_bytes(data) {
        Ok((probe_id, compact_item_iterator, ext_bytes)) => {
            let log: Vec<_> = compact_item_iterator.collect();
            use modality_probe::{BulkReporter, ExtensionBytes};
            let mut destination = vec![0u8; data.len()];
            let n_report_bytes = modality_probe::report::bulk::BulkReportSourceComponents {
                probe_id,
                log: &log,
            }
            .report_with_extension(&mut destination, ExtensionBytes(ext_bytes.0))
            .unwrap();
            let (round_trip_id, round_trip_item_iterator, round_trip_ext_bytes) =
                modality_probe::report::bulk::try_bulk_from_wire_bytes(
                    &destination[..n_report_bytes],
                )
                .unwrap();
            assert_eq!(probe_id, round_trip_id);
            let round_trip_log: Vec<_> = round_trip_item_iterator.collect();
            assert_eq!(log, round_trip_log);
            assert_eq!(ext_bytes.0, round_trip_ext_bytes.0);
        }
        Err(_) => (),
    };
});
