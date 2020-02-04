#!/bin/sh

set -ex
rm -f Cargo.lock
cargo clean

(
    cd ekotrace-capi
    rm -f Cargo.lock
    cargo clean
)

(
    cd examples/event-recording/
    rm -f tracers.csv events.csv tracing_ids.rs
)
