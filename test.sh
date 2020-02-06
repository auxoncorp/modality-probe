#!/bin/sh

set -ex

(
    cd examples/event-recording/
    cargo run -p ekotrace-cli -- manifest-gen --events-csv-file events.csv --tracers-csv-file tracers.csv ./
    cargo run -p ekotrace-cli -- header-gen --lang Rust events.csv tracers.csv > tracing_ids.rs
)

cargo build --all
cargo test --workspace

(
    cd ekotrace-capi
    cargo test
)

(
    cd ekotrace-capi/ctest
    ./build_and_run
)
