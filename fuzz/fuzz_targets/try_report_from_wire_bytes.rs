#![no_main]
use libfuzzer_sys::fuzz_target;
use modality_probe::wire::report::WireReport;

fuzz_target!(|data: &[u8]| {
    match WireReport::new(data) {
        Ok(r) => {
            assert_eq!(r.fingerprint(), WireReport::<&[u8]>::FINGERPRINT);
            // hit all of the getters to make sure the report is usable without
            // panicing
            let _ = r.probe_id();
            let _ = r.clock();
            let _ = r.seq_num();
            let _ = r.persistent_epoch_counting();
            let _ = r.time_resolution();
            let _ = r.wall_clock_id();
            let _ = r.n_clocks();
            let _ = r.n_log_entries();
            let _ = r.payload_len();
            let _ = r.payload();
        }
        Err(_) => (),
    };
});
