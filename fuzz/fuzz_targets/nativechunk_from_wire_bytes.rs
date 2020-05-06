#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _res = ekotrace::report::chunked::NativeChunk::from_wire_bytes(data);
});
