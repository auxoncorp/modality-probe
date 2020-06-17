#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = modality_probe::report::bulk::try_bulk_from_wire_bytes(data);
});
