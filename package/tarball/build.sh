#!/bin/bash
#
# Build dependencies:
# * tar
# * rustup component add llvm-tools-preview
# * cargo install cross

set -ex

PACKAGE_NAME="modality-probe_$(git describe --always)"

TARBALL_FILE="${PACKAGE_NAME}.tar.gz"

LIBRARY_TARGET_TRIPLES=(
"thumbv7em-none-eabi"
"arm-unknown-linux-gnueabi"
"aarch64-unknown-linux-gnu"
"x86_64-unknown-linux-gnu")

BINARY_TARGET_TRIPLE="x86_64-unknown-linux-musl"

WORKSPACE_ROOT="../.."

OUTPUT_DIR="${OUTPUT_DIR:=target/package/tarball}"

LLVM_STRIP=`find $(rustc --print sysroot) -name llvm-strip`

# Cleanup
(
    cd "$WORKSPACE_ROOT"
    rm -rf "$OUTPUT_DIR"
    mkdir -p "$OUTPUT_DIR"
)

# Build the binaries for the host, used to generate man pages and completions
(
    cd "$WORKSPACE_ROOT"

    cargo build --release \
        -p modality-probe-cli --bin modality-probe

    cargo build --release \
        -p modality-probe-udp-collector --bin modality-probe-udp-collector
    
    cargo build --release \
        -p modality-probe-debug-collector --bin modality-probe-debug-collector
)

# Build the binaries for the target
(
    cd "$WORKSPACE_ROOT"

    cross build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-cli --bin modality-probe

    cross build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-udp-collector --bin modality-probe-udp-collector

    # Requires toolchain of target binary to be installed
    PKG_CONFIG_ALLOW_CROSS=1 cargo build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-debug-collector --bin modality-probe-debug-collector

    $LLVM_STRIP --strip-unneeded --strip-debug \
        "target/$BINARY_TARGET_TRIPLE/release/modality-probe"

    $LLVM_STRIP --strip-unneeded --strip-debug \
        "target/$BINARY_TARGET_TRIPLE/release/modality-probe-udp-collector"

    $LLVM_STRIP --strip-unneeded --strip-debug \
        "target/$BINARY_TARGET_TRIPLE/release/modality-probe-debug-collector"

    mkdir -p "$OUTPUT_DIR/$PACKAGE_NAME/bin"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe" \
        "$OUTPUT_DIR/$PACKAGE_NAME/bin/"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe-udp-collector" \
        "$OUTPUT_DIR/$PACKAGE_NAME/bin/"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe-debug-collector" \
        "$OUTPUT_DIR/$PACKAGE_NAME/bin/"

    chmod 755 "$OUTPUT_DIR/$PACKAGE_NAME/bin/"*
)

# Build the libraries
(
    cd "$WORKSPACE_ROOT"

    toolchain=`cat modality-probe-capi/rust-toolchain`

    for triple in "${LIBRARY_TARGET_TRIPLES[@]}"; do
        mkdir -p "$OUTPUT_DIR/$PACKAGE_NAME/lib/$triple"

        RUSTUP_TOOLCHAIN="$toolchain" cross build \
            --manifest-path "modality-probe-capi/Cargo.toml" \
            --release --target "$triple"

        $LLVM_STRIP --strip-debug "target/$triple/release/libmodality_probe.a"
        cp -a "target/$triple/release/libmodality_probe.a" \
            "$OUTPUT_DIR/$PACKAGE_NAME/lib/$triple/"

        if [ -f "target/$triple/release/libmodality_probe.so" ]; then
            $LLVM_STRIP --strip-unneeded --strip-debug "target/$triple/release/libmodality_probe.so"
            cp -a "target/$triple/release/libmodality_probe.so" \
                "$OUTPUT_DIR/$PACKAGE_NAME/lib/$triple/"
        fi

        chmod 644 "$OUTPUT_DIR/$PACKAGE_NAME/lib/$triple/"*
    done
)

# Copy C header files
(
    cd "$WORKSPACE_ROOT"

    mkdir -p "$OUTPUT_DIR/$PACKAGE_NAME/include/modality"
    cp -a "modality-probe-capi/include/probe.h" "$OUTPUT_DIR/$PACKAGE_NAME/include/modality/"

    chmod 644 "$OUTPUT_DIR/$PACKAGE_NAME/include/modality/"*
)

# Copy license/docs
(
    cd "$WORKSPACE_ROOT"

    mkdir -p "$OUTPUT_DIR/$PACKAGE_NAME/doc"
    cp -a LICENSE "$OUTPUT_DIR/$PACKAGE_NAME/doc/"
    cp -a CHANGELOG.md "$OUTPUT_DIR/$PACKAGE_NAME/doc/"

    chmod 644 "$OUTPUT_DIR/$PACKAGE_NAME/doc/"*
)

# Build the man pages
(
    cd "$WORKSPACE_ROOT"

    man_dir="$OUTPUT_DIR/$PACKAGE_NAME/man1"
    mkdir -p "$man_dir"

    help2man --no-info "target/release/modality-probe" \
        > "$man_dir/modality-probe.1"
    help2man --no-info "target/release/modality-probe-udp-collector" \
        > "$man_dir/modality-probe-udp-collector.1"
    help2man --no-info "target/release/modality-probe-debug-collector" \
        > "$man_dir/modality-probe-debug-collector.1"

    gzip --no-name --best "$man_dir/modality-probe.1"
    gzip --no-name --best "$man_dir/modality-probe-udp-collector.1"
    gzip --no-name --best "$man_dir/modality-probe-debug-collector.1"

    chmod 644 "$man_dir/"*
)

# Build the completions
(
    cd "$WORKSPACE_ROOT"

    comp_dir="$OUTPUT_DIR/$PACKAGE_NAME/completions"
    mkdir -p "$comp_dir"

    cargo run --release \
        -p modality-probe-cli --bin modality-probe-completions
    cargo run --release \
        -p modality-probe-udp-collector --bin modality-probe-udp-collector-completions
    cargo run --release \
        -p modality-probe-debug-collector --bin modality-probe-debug-collector-completions

    mv modality-probe.bash "$comp_dir/"
    mv modality-probe-udp-collector.bash "$comp_dir/"
    mv modality-probe-debug-collector.bash "$comp_dir/"

    chmod 644 "$comp_dir/"*
)

# Tar it up
(
    cd "$WORKSPACE_ROOT"
    cd "$OUTPUT_DIR"

    rm -f "$TARBALL_FILE"

    tar -czf "$TARBALL_FILE" "$PACKAGE_NAME/"
)

exit 0
