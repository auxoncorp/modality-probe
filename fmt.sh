#!/bin/sh

set -ex
cargo fmt --all

(
    cd ekotrace-capi
    cargo fmt
)
