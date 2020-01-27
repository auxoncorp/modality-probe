#!/bin/sh

set -ex
rm -f Cargo.lock
cargo clean

(
    cd ekotrace-capi
    rm -f Cargo.lock
    cargo clean
)
