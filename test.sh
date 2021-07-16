#!/bin/sh

set -ex

cargo build --all
cargo test --workspace --features "std, debug-collector-access"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test --workspace
)

# This is just to make sure that the fuzz tests actually /can/ build and run
for target in `cargo fuzz list`; do
     RUSTUP_TOOLCHAIN=nightly-2021-03-01 cargo fuzz run $target -- -max_total_time=1s
done
