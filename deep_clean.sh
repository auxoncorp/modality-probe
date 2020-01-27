#!/bin/sh

set -ex
rm Cargo.lock
cargo clean

(
    cd ekotrace-capi
    rm Cargo.lock
    cargo clean
)
