#!/bin/sh

set -ex

cargo build --all
cargo test

(
    cd ekotrace-analysis
    cargo test
)

(
    cd ekotrace-manifest-gen
    cargo test
)

(
    cd ekotrace-capi
    cargo test
)

(
    cd ekotrace-capi/ctest
    ./build_and_run
)
