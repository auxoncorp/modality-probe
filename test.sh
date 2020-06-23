#!/bin/sh

set -ex

(
    cd examples/
    rm -f events.csv probes.csv
    mkdir -p generated_ids/
    cargo run -p modality-probe-cli -- manifest-gen --events-csv-file events.csv --probes-csv-file probes.csv ./
    cargo run -p modality-probe-cli -- header-gen --lang Rust events.csv probes.csv --output-path generated_ids/mod.rs
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
