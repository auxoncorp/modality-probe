# ekotrace-capi

This crate exports a static or dynamic library for use in C projects.

The API is defined through the [ekotrace header file](include/ekotrace.h)
and implemented as a Rust project with Cargo.

## API

See the header file for documentation of available functions.

## Building

This library requires a [Rust](https://www.rust-lang.org/) toolchain.
The recommended toolchain management system in Rust is [rustup](https://rustup.rs).

Once rustup is installed, you can build for your local device with:

```shell script
cargo build
```

And the output artifact will be located in target/debug/libekotrace_capi.*

Optimized libraries can be built with

```shell script
cargo build --release
```

and are located at target/release/libekotrace_capi.*

### Cross Platform Builds

In order to build this library for other platforms, we recommend the use
of [cargo-xbuild](https://github.com/rust-osdev/cargo-xbuild).

See that project for detailed instructions. The likely default usage
path for obtaining a new target's toolchain and building for it is:

```shell script
rustup update
cargo install cargo-xbuild --force
rustup target add thumbv7em-none-eabi
rustc -Z unstable-options --print target-spec-json --target thumbv7em-none-eabi | tee thumbv7em-none-eabi.json
cargo xbuild --target thumbv7em-none-eabi.json
```

The output artifacts for `cargo xbuild` invocations live within a slightly
different path in the target directory, target/thumbv7em-none-eabi/debug/* in this case.

Substitute "thumbv7em-none-eabi" for your target of interest.

