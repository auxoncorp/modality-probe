#!/bin/sh

set -ex
rm Cargo.lock
cargo clean --all

(
    cd ekotrace-capi
    rm Cargo.lock
    cargo clean
)
