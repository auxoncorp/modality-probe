# `modality-probe`

`modality-probe` is an open source part of Auxon’s Modality™
continuous verification & validation platform. Its role is to record
events and track their causal relationships between the different
parts of your system. Why? Because being able to stitch together a
causal history of a system, particularly a system _under test_,
provides a high-resolution lens into _what happened_. This history can
then be used for testing, debugging, understanding emergent scenarios,
and more.

While `modality-probe` is written in Rust, it targets C environments,
particularly those of the embedded variety. The library used for
recording events and exchanging causality data does not depend on any
sort of standard library and could be used in bare-metal or RTOS
environments.

## How do I use it?

### Have Rust

Clone this repository, and start by navigating into its root folder.
Then use [`rustup`](https://rustup.rs/), then you should have the
cargo command available to you and the commands in the following
section should work.

### Build it

#### Linux (Debian-flavored)

Install `cargo-deb`, a cargo subcommand that can convert a Cargo crate
into a debian package.

```shell
modality-probe $ cargo install cargo-deb
```

Navigate into the `debian` folder beneath `package` and run the build
script that's there.

```shell
modality-probe $ cd package/debian
modality-probe/packing/debian $ ./build.sh
```

It will build all of the components of `modality-probe`, the
[library](./modality-probe-capi/README.md), the
[cli](./modality-probe-cli/README.md), and the [UDP
collector](./collectors/modality-probe-udp-collector/README.md) and package them
up into a deb file which you can find in `target/debian` from your
current working directory. It can then be installed in the usual way,
with `dpkg`.

```shell
modality-probe/packing/debian $ dpkg -i target/debian/modality-probe_<version>_<arch>.deb
```

Now you're ready to hack.

#### Other *nixes (*nices?)

Cargo can use something called "workspaces" to build groups of
libraries or applications that share a source tree. `modality-probe`
uses workspaces, and we can ask cargo to build all of the members of a
workspace with the `--all` switch:

```shell
modality-probe $ cargo build --release --all
```

Once that's finished, if you're targeting a C application, you'll want
to build `modality-probe-capi`, it's what builds the C-linkable `.so`
and `.a` that you can link into your C application. We'll run the same
command modulo the `--all` switch from its directory.

```shell
modality-probe/modality-probe-capi $ cargo build --release
```

Now you should find the cli and the udp collector in the root
`target/release` directory, and the `.so` / `.a` for
`libmodality_probe` in the C API's `target/release` directory. Move
these to, respectively, `$PATH` and somewhere that your linker can
find them.

#### Windows

_sighs deeply._ Something, something, dot exe.

### Use it

TODO: payloads, now, collector, jon's tracing example?, cli export

#### In C

You first need to initialize your tracer.

```c
int main() {
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe_error result = modality_probe_initialize(
        destination,
        DEFAULT_PROBE_SIZE,
        CONTROLLER,
        probe_g
    );
}
```

Then you can use it to record events.

```c
#define DEFAULT_PROBE_SIZE = 7000;
modality_probe * probe_g = MODALITY_PROBE_NULL_INITIALIZER;

void twist(double x, double y, double z) {
    int result = MODALITY_PROBE_RECORD(
        probe_g,
        TWISTED,
        TAGS("actuation"),
        "A twist command was received"
    );
    // …
}
```

#### In Rust

You first need to initialize your tracer.

```rust
fn main() {
    let mut storage = [0u8; 1024];
    let tracer = try_initialize_at!(&mut storage, LID_B, TAGS("actuation"), "Twister")
        .expect("Could not initialize Ekotrace");
    // …
}
```

Then you can use it to record events.

```rust
fn twist(x: f64, y: f64, z: f64) -> Result<(), TwistError> {
    // …
    try_record!(
        tracer,
        GOING_TO_DO_A_TWIST,
        tags!("actuation"),
        "A twist is going to happen",
    )?;
    // …
}
```

## Reading more

See each subcrate's local readme for more information.
