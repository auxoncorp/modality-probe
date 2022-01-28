#!/bin/sh

set -ex

cargo build --all
cargo test --features "serde"
cargo test --features "std schemars"
cargo test --features "debug-collector-access"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test --workspace
)

# This is just to make sure that the fuzz tests actually /can/ build and run
PINNED_NIGHTLY=`cat modality-probe-capi/rust-toolchain`
(
    export RUSTUP_TOOLCHAIN=$PINNED_NIGHTLY
    for target in `cargo fuzz list`; do
         cargo fuzz run $target -- -max_total_time=1s
    done
)
