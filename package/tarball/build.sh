#!/bin/bash
#
# Build dependencies:
# * tar
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
