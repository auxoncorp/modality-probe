#!/bin/sh

set -ex

cargo build --all
cargo test --no-run --workspace --features "std"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test --workspace
)

(
    cd examples/rust-example/
    cargo test
)

# Windows MSVC doesn't like the no-std modality-probe-capi cdylib build
if [ $# -ne 0 ]; then
    if [ "$1" = "windows" ]; then
        exit 0
    fi
fi

(
    cd modality-probe-capi/ctest
    ./build_and_run
)
