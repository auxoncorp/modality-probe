#!/bin/sh

set -ex

cargo fmt

(
    cd truce-c
    cargo fmt
)
