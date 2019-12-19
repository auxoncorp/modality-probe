#!/bin/sh

set -ex

cargo build --all
cargo test

(
    cd truce-c
    cargo test
)

(
    cd truce-c/ctest
    ./build_and_run
)
