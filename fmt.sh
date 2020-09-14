#!/bin/sh

set -ex
cargo fmt --all

(
    cd modality-probe-capi
    cargo fmt
)

(
    cd examples/rust-example/
    cargo fmt
)
