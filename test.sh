#!/bin/sh

set -ex

cargo build --all
cargo test --workspace --features "std, debug-collector-access"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test --workspace
)

(
    cd modality-probe-capi/ctest
    make test
)

(
    cd examples/rust-example/
    cargo test
)

(
    cd examples/c-example/

    # The C example's integration test bash script isn't windows friendly yet,
    # we just build and run the example on windows for now
    if [ $# -ne 0 ] && [ "$1" = "windows" ]; then
        make run
    else
        make test
    fi
)

# This is just to make sure that the fuzz tests actually /can/ build and run
for target in `cargo fuzz list`; do
     RUSTUP_TOOLCHAIN=nightly-2020-10-07 cargo fuzz run $target -- -max_total_time=1s
done
