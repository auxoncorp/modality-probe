#!/bin/bash
#
# Build dependencies:
# * tar
# * help2man
# * gzip
# * rustup component add llvm-tools-preview
# * cargo install cross

set -ex

LIBRARY_TARGET_TRIPLES=(
"thumbv7em-none-eabi"
"arm-unknown-linux-gnueabi"
"aarch64-unknown-linux-gnu"
"x86_64-unknown-linux-gnu")

BINARY_TARGET_TRIPLE="x86_64-unknown-linux-musl"

WORKSPACE_ROOT="../.."

OUTPUT_DIR="${OUTPUT_DIR:=target/package/tarball}"

LLVM_STRIP=`find $(rustc --print sysroot) -name llvm-strip`

VERSION=`cat $WORKSPACE_ROOT/VERSION`
SHORTVERSION=${VERSION%.*}
MAJVERSION=${SHORTVERSION%.*}
PACKAGE_VERSION="$VERSION"

if [ ! -x $LLVM_STRIP ] || [ -z $LLVM_STRIP ]; then
    echo "Can't find llvm-strip"
    exit 1
fi

# Nightly builds get a build number in the version
if [[ -n "$GITHUB_RUN_NUMBER" && -n "$GITHUB_WORKFLOW" ]]; then
    if [ "$GITHUB_WORKFLOW" == "Nightly Build" ]; then
        # See semver section 10 about build metadata
        PACKAGE_VERSION+="+$GITHUB_RUN_NUMBER"
    fi
fi

PACKAGE_NAME="modality-probe_$PACKAGE_VERSION"
PACKAGE_PATH="$OUTPUT_DIR/$PACKAGE_NAME"

TARBALL_FILE="${PACKAGE_NAME}.tar.gz"

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

    cargo build --release \
        -p modality-probe-offline-batch-collector --bin modality-probe-offline-batch-collector
)

# Build the binaries for the target
(
    cd "$WORKSPACE_ROOT"

    cross build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-cli --bin modality-probe

    cross build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-udp-collector --bin modality-probe-udp-collector

    cross build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-offline-batch-collector --bin modality-probe-offline-batch-collector

    # Requires toolchain of target binary to be installed
    PKG_CONFIG_ALLOW_CROSS=1 cargo build --release --target "$BINARY_TARGET_TRIPLE" \
        -p modality-probe-debug-collector --bin modality-probe-debug-collector

    mkdir -p "$PACKAGE_PATH/bin"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe" \
        "$PACKAGE_PATH/bin/"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe-udp-collector" \
        "$PACKAGE_PATH/bin/"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe-debug-collector" \
        "$PACKAGE_PATH/bin/"
    cp -a "target/$BINARY_TARGET_TRIPLE/release/modality-probe-offline-batch-collector" \
        "$PACKAGE_PATH/bin/"

    $LLVM_STRIP --strip-unneeded --strip-debug "$PACKAGE_PATH/bin/modality-probe"

    $LLVM_STRIP --strip-unneeded --strip-debug "$PACKAGE_PATH/bin/modality-probe-udp-collector"

    $LLVM_STRIP --strip-unneeded --strip-debug "$PACKAGE_PATH/bin/modality-probe-debug-collector"

    $LLVM_STRIP --strip-unneeded --strip-debug "$PACKAGE_PATH/bin/modality-probe-offline-batch-collector"

    chmod 755 "$PACKAGE_PATH/bin/"*
)

# Build the libraries
(
    cd "$WORKSPACE_ROOT"

    toolchain=`cat modality-probe-capi/rust-toolchain`

    for triple in "${LIBRARY_TARGET_TRIPLES[@]}"; do
        arch_lib_path="$PACKAGE_PATH"/lib/"$triple"
        build_path=target/"$triple"/release

        mkdir -p "$arch_lib_path"

        RUSTUP_TOOLCHAIN="$toolchain" cross build \
            --manifest-path "modality-probe-capi/Cargo.toml" \
            --release --target "$triple"

        cp "$build_path"/libmodality_probe.a "$arch_lib_path"/libmodality_probe.a
        $LLVM_STRIP --strip-debug "$arch_lib_path"/libmodality_probe.a

        if [ -f "$build_path"/libmodality_probe.so ]; then
            cp "$build_path"/libmodality_probe.so "$arch_lib_path"/libmodality_probe.so."$VERSION"
            $LLVM_STRIP --strip-unneeded --strip-debug "$arch_lib_path"/libmodality_probe.so."$VERSION"
            (
                cd "$arch_lib_path"
                ln -sf libmodality_probe.so."$VERSION" libmodality_probe.so."$MAJVERSION"
                ln -sf libmodality_probe.so."$MAJVERSION" libmodality_probe.so
            )
        fi

        chmod 644 "$arch_lib_path/"*
    done
)

# Copy C header files
(
    cd "$WORKSPACE_ROOT"

    mkdir -p "$PACKAGE_PATH/include/modality"
    cp -a "modality-probe-capi/include/probe.h" "$PACKAGE_PATH/include/modality/"

    chmod 644 "$PACKAGE_PATH/include/modality/"*
)

# Copy license/docs
(
    cd "$WORKSPACE_ROOT"

    mkdir -p "$PACKAGE_PATH/doc"
    cp -a LICENSE "$PACKAGE_PATH/doc/"
    cp -a CHANGELOG.md "$PACKAGE_PATH/doc/"

    chmod 644 "$PACKAGE_PATH/doc/"*
)

# Build the man pages
(
    cd "$WORKSPACE_ROOT"

    man_dir="$PACKAGE_PATH/man1"
    mkdir -p "$man_dir"

    help2man --version-string="$VERSION" --no-info "target/release/modality-probe" \
        > "$man_dir/modality-probe.1"
    help2man --version-string="$VERSION" --no-info "target/release/modality-probe-udp-collector" \
        > "$man_dir/modality-probe-udp-collector.1"
    help2man --version-string="$VERSION" --no-info "target/release/modality-probe-debug-collector" \
        > "$man_dir/modality-probe-debug-collector.1"
    help2man --version-string="$VERSION" --no-info "target/release/modality-probe-offline-batch-collector" \
        > "$man_dir/modality-probe-offline-batch-collector.1"

    gzip --no-name --best "$man_dir/modality-probe.1"
    gzip --no-name --best "$man_dir/modality-probe-udp-collector.1"
    gzip --no-name --best "$man_dir/modality-probe-debug-collector.1"
    gzip --no-name --best "$man_dir/modality-probe-offline-batch-collector.1"

    chmod 644 "$man_dir/"*
)

# Build the completions
(
    cd "$WORKSPACE_ROOT"

    comp_dir="$PACKAGE_PATH/completions"
    mkdir -p "$comp_dir"

    cargo run --release \
        -p modality-probe-cli --bin modality-probe-completions
    cargo run --release \
        -p modality-probe-udp-collector --bin modality-probe-udp-collector-completions
    cargo run --release \
        -p modality-probe-debug-collector --bin modality-probe-debug-collector-completions
    cargo run --release \
        -p modality-probe-offline-batch-collector --bin modality-probe-offline-batch-collector-completions

    mv modality-probe.bash "$comp_dir/"
    mv modality-probe-udp-collector.bash "$comp_dir/"
    mv modality-probe-debug-collector.bash "$comp_dir/"
    mv modality-probe-offline-batch-collector.bash "$comp_dir/"

    chmod 644 "$comp_dir/"*
)

# Copy CMake scripts
(
    cd "$WORKSPACE_ROOT"
    cp -a "package/cmake" "$PACKAGE_PATH/"
)

# Version
(
    cd "$WORKSPACE_ROOT"
    echo "$VERSION" > "$PACKAGE_PATH/VERSION"
)

# Tar it up
(
    cd "$WORKSPACE_ROOT"
    cd "$OUTPUT_DIR"

    rm -f "$TARBALL_FILE"

    tar -czf "$TARBALL_FILE" "$PACKAGE_NAME/"
)

exit 0
