#!/bin/sh

set -ex
rm -f Cargo.lock
cargo clean

(
    cd modality-probe-capi
    rm -f Cargo.lock
    cargo clean

    cd ctest
    make clean
)

(
    cd fuzz
    cargo clean
)
