#![no_main]
use libfuzzer_sys::fuzz_target;
use modality_probe::wire::report::WireReport;

fuzz_target!(|data: &[u8]| {

    if let Ok(r) = WireReport::new(data) {
        if let Ok(probe_id) = r.probe_id() {
            // Transcribe the decoded data to a report in a different buffer
            let mut other_buffer = vec![0u8; data.len()];
            {
                let mut other_report = WireReport::new_unchecked(&mut other_buffer);

                other_report.set_fingerprint();
                other_report.set_probe_id(probe_id);
                other_report.set_clock(r.clock());
                other_report.set_seq_num(r.seq_num());
                other_report.set_raw_persistent_epoch_counting(r.raw_persistent_epoch_counting());
                other_report.set_time_resolution(r.time_resolution());
                other_report.set_wall_clock_id(r.wall_clock_id());
                other_report.set_n_clocks(r.n_clocks());
                other_report.set_n_log_entries(r.n_log_entries());
                assert_eq!(other_report.check_fingerprint(), Ok(()));
                assert_eq!(other_report.check_payload_len(), Ok(()));

                let source_payload_slice = &r.payload()[..r.payload_len()];
                let dest_payload_slice = &mut other_report.payload_mut()[..r.payload_len()];
                dest_payload_slice.copy_from_slice(source_payload_slice);
            }

            // compare the relevant portion of the buffers
            // (magic number from report::field::PAYLOAD.start)
            let report_data_size = WireReport::<&[u8]>::header_len() + r.payload_len();
            assert_eq!(&data[..report_data_size], &other_buffer[..report_data_size]);
        }
    }
});
