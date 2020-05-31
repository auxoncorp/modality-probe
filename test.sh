#!/bin/sh

set -ex

(
    cd examples/
    rm -f events.csv tracers.csv
    mkdir -p tracing_ids/
    cargo run -p ekotrace-cli -- manifest-gen --events-csv-file events.csv --tracers-csv-file tracers.csv ./
    cargo run -p ekotrace-cli -- header-gen --lang Rust events.csv tracers.csv > tracing_ids/mod.rs
)

cargo build --all
cargo test --no-run --workspace --features "std"
cargo test --workspace

(
    cd ekotrace-capi
    cargo test
)

# Windows MSVC doesn't like the no-std ekotrace-capi cdylib build
if [ $# -ne 0 ]; then
    if [ "$1" = "windows" ]; then
        exit 0
    fi
fi

(
    cd ekotrace-capi/ctest
    ./build_and_run
)
