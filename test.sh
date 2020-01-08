#!/bin/sh

set -ex

cargo build --all
cargo test

(
    cd truce/truce-c
    cargo test
)

(
    cd truce/truce-c/ctest
    ./build_and_run
)
