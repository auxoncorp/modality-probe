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
    cd examples
    rm -rf example-component generated_ids/mod.rs
)

(
    cd fuzz
    cargo clean
)

(
    cd package/debian
    cargo clean
    rm -f Cargo.lock
)
