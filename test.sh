#!/bin/sh

set -ex

(
    cd examples/event-recording/
    cargo run -p ekotrace-manifest-gen -- --events-csv-file events.csv --tracers-csv-file tracers.csv ./
    cargo run -p ekotrace-header-gen -- --lang Rust events.csv tracers.csv > tracing_ids.rs
)

cargo build --all
cargo test

(
    cd ekotrace-analysis
    cargo test
)

(
    cd ekotrace-manifest-gen
    cargo test
)

(
    cd ekotrace-capi
    cargo test
)

(
    cd ekotrace-capi/ctest
    ./build_and_run
)
