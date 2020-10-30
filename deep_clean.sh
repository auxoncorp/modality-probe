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
    cd examples/rust-example/
    cargo clean
    rm -rf example-component src/component_definitions.rs Cargo.lock
)

(
    cd examples/c-example/
    make clean
    rm -rf example-component include/component_definitions.h
)

(
    cd collectors/modality-probe-debug-collector/tests/empty-example
    cargo clean
)

(
    cd collectors/modality-probe-debug-collector/tests/symbols-example
    cargo clean
)

(
    cd fuzz
    cargo clean
)
