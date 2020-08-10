#!/bin/bash

set -ex

(
    cd ../../
    cargo build --release -p modality-probe-cli --bin modality-probe
    cargo build --release -p modality-probe-udp-collector --bin modality-probe-udp-collector

    strip --strip-unneeded target/release/modality-probe
    strip --strip-unneeded target/release/modality-probe-udp-collector
)

(
    cd ../../modality-probe-capi
    cargo build --release

    strip --strip-unneeded target/release/libmodality_probe.so
    strip --strip-debug target/release/libmodality_probe.a
)

rm -rf target/man1
mkdir -p target/man1

help2man --no-info ../../target/release/modality-probe > "target/man1/modality-probe.1"
help2man --no-info ../../target/release/modality-probe-udp-collector > "target/man1/modality-probe-udp-collector.1"

gzip --no-name --best "target/man1/modality-probe.1"
gzip --no-name --best "target/man1/modality-probe-udp-collector.1"

rm -rf target/completions
mkdir -p target/completions

(
    cd ../../
    cargo run -p modality-probe-cli --bin modality-probe-completions
    cargo run -p modality-probe-udp-collector --bin modality-probe-udp-collector-completions
)

mv ../../modality-probe.bash target/completions/
mv ../../modality-probe-udp-collector.bash target/completions/

cargo deb --no-build
