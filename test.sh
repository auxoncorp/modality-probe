#!/bin/sh

set -ex

(
    cd examples/
    rm -f events.csv probes.csv Component.toml
    mkdir -p generated_ids/
    cargo run -p modality-probe-cli -- manifest-gen --file-extension="rs" --output-path example-component .
    cargo run -p modality-probe-cli -- header-gen --lang Rust --output-path generated_ids/mod.rs example-component
)

cargo build --all
cargo test --no-run --workspace --features "std"
cargo test --workspace

(
    cd modality-probe-capi
    cargo test --workspace
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
