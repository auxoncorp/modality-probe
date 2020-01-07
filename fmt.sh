#!/bin/sh

set -ex
cargo fmt --all

(
    cd truce/truce-c
    cargo fmt
)
