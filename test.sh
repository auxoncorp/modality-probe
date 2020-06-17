#!/bin/sh

set -ex

(
    cd examples/
    rm -f events.csv tracers.csv
    mkdir -p tracing_ids/
    cargo run -p modality-probe-cli -- manifest-gen --events-csv-file events.csv --tracers-csv-file tracers.csv ./
    cargo run -p modality-probe-cli -- header-gen --lang Rust events.csv tracers.csv --output-path tracing_ids/mod.rs
)

cargo build --all
cargo test --no-run --workspace --features "std"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test
)

# Windows MSVC doesn't like the no-std modality-probe-capi cdylib build
if [ $# -ne 0 ]; then
    if [ "$1" = "windows" ]; then
        exit 0
    fi
fi

(
    cd modality-probe-capi/ctest
    ./build_and_run
)
