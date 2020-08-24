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
sort of standard library and is fully functional in bare-metal or RTOS
environments.

## How do I use it?

### Have Rust

Clone this repository, and start by navigating into its root folder.
If you don't have Rust installed, the recommended way to do so is with
[`rustup`](https://rustup.rs/). After following the directions at that
link, you should have the `cargo` command available to you and the
commands in the following section should work.

### Build It

#### Linux

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

### Integrate It

#### In C

You first need to initialize your probe.

```c
#include <modality/probe.h>

/* Output of the CLI's header-gen sub-command */
#include "generated_component_ids.h"

/* The probe will be given 1024 bytes of storage space to work with */
#define DEFAULT_PROBE_SIZE (1024)
static uint8_t g_probe_buffer[DEFAULT_PROBE_SIZE];

/* The probe instance, global for convenience */
static modality_probe *g_probe = MODALITY_PROBE_NULL_INITIALIZER;

int main(int argc, char **argv)
{
    size_t err = MODALITY_PROBE_INIT(
            &g_probe_buffer[0],
            DEFAULT_PROBE_SIZE,
            CONTROLLER,
            NULL, /* This probe does not track probe restarts */
            NULL,
            &g_probe,
            MODALITY_TAGS("controller"),
            "The controller");

    /* ... */
}
```

Then you can use it to record events.

```c
#include <modality/probe.h>

/* Output of the CLI's header-gen sub-command */
#include "generated_ids.h"

void do_twist_command(void)
{
    size_t err = MODALITY_PROBE_RECORD(
            g_probe,
            TWISTED,
            MODALITY_TAGS("actuation"),
            "A twist command was received");
    assert(err == MODALITY_PROBE_ERROR_OK);

    /* ... */
}
```

#### In Rust

You first need to initialize your tracer.

```rust
const LOG_STORAGE_SIZE: usize = 1024;

fn main() {
    let mut storage = [0u8; LOG_STORAGE_SIZE];
    let tracer = try_initialize_at!(
        &mut storage,
        LID_B,
        RestartCounterProvider::NoRestartTracking,
        tags!("actuation"),
        "Twister"
    ).expect("Could not initialize Ekotrace");
    // …
}
```

Then you can use it to record events.

```rust
use modality_probe::try_record;

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


<!-- TODO: CLI, payloads, now, collector, jon's tracing example?, cli export -->


## Reading more

See each subcrate's local readme for more information.
