#!/bin/sh

set -ex
rm -f Cargo.lock
cargo clean

(
    cd modality-probe-capi
    rm -f Cargo.lock
    cargo clean
)

(
    cd examples/
    rm -f tracers.csv events.csv generated_ids/mod.rs
)

(
    cd fuzz/
    cargo clean
)
