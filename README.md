# modality-probe

An embedded-friendly causal tracing system.

## Overview

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

## Getting Started

### Dependencies

#### Rust

If you don't have Rust installed, the recommended way to do so is with
[`rustup`](https://rustup.rs/). After following the directions at that
link, you should have the `cargo` command available to you and the
commands in the following section should work.

### Building

#### Linux

Clone this repository, and start by navigating into its root folder.
Then use Cargo to build the Modality Probe libraries and their related
binaries.

```shell
modality-probe $ cargo build --release --all
```

If you're targeting a C application, you'll also want to build
`modality-probe-capi`, it's what builds the C-linkable `.so` and `.a`
that you can link into your C application. We'll run the same command
modulo the `--all` switch from its directory.

```shell
modality-probe/modality-probe-capi $ cargo build --release
```

Now you should find the cli and the udp collector in the root
`target/release` directory, and the `.so` / `.a` for
`libmodality_probe` in the C API's `target/release` directory. Move
these to, respectively, `$PATH` and somewhere that your linker can
find them. On Linux, you can use `ldconfig` to see where the linker
searches:

```shell
# ldconfig -v 2>/dev/null | grep ^/ | tr -d ':'
```

### Usage

#### Instrumenting In C

Begin by initializing your probe:

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

Then, you can use your initialized probe to record events.

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

#### Instrumenting In Rust

Begin by initializing your probe:

```rust
use modality_probe::{try_initialize_at, tags, RestartCounterProvider};

// Output of the CLI's header-gen sub-command
use generated_component_ids::*;

const DEFAULT_PROBE_SIZE: usize = 1024;

fn main() {
    let mut probe_buffer = [0u8; DEFAULT_PROBE_SIZE];

    let tracer = try_initialize_at!(
        &mut probe_buffer,
        CONTROLLER,
        RestartCounterProvider::NoRestartTracking,
        tags!("controller"),
        "The controller"
    ).expect("Could not initialize probe");

    // …
}
```

Then, you can use your initialized probe to record events.

```rust
use modality_probe::try_record;

// Output of the CLI's header-gen sub-command
use generated_component_ids::*;

pub fn do_twist_command(&mut self) -> Result<(), TwistError> {
    try_record!(
        self.probe,
        TWISTED,
        tags!("actuation"),
        "A twist command was received",
    )?;

    // …
}
```

### Generate Event Manifests and Definitions

In the samples above, a macro is used to initialize a probe and to
record events. Modality Probe's CLI has a subcommand that explores
your code base for uses of these macros and turns those uses into what
Modality calls a _Component_. A component has a name of its own, a
list of probes (`probes.csv`), and a list of events
(`events.csv`). Altogether, a component looks like this:

```
$ tree my-component
├── Component.toml
├── events.csv
└── probes.csv
```

`manifest-gen` is the subcommand we use to do this. Use it like this:

```shell
$ modality-probe manifest-gen --component-name my-component -o my-component .
```

Now you'll have the `my-component` directory in your working directory
and its contents should look like the example at the top of this
section.

Next, we'll want to generate the source code that gives those symbols
we discussed in the code snippet examples in the previous section
their definitions. To do that, we'll use `header-gen`:

```shell
$ modality-probe header-gen -o include/events.h my-component
```

This will deposit a file at `include/events.h` that contains
definitions for each probe and event in the manifests in your
component.

If you're using Rust, you can tell the command to generate Rust
instead using the `--lang` switch (C is the default):

```shell
$ modality-probe header-gen -o include/events.rs -l rust my-component
```

### Collect Outgoing Reports

Modality Probe also ships with a service that can collect via UDP the
reports you generate from your probes. It writes those incoming
reports as JSON lines to a file. Start it like so:

```shell
$ modality-probe-udp-collector
Using the configuration:
    addr: 0.0.0.0:2718
    session id: 0
    output file: /home/me/src/my-project/session_0_log_entries.jsonl

```

When the service starts it prints the configuration it's using. In
the example above it's using all defaults. You can also pass args to
direct it to a certain port, or a specific output file.

To get data out to a collector, you need to use the Probe's `report`
API, and then send the report that that API creates along to your
collector.

That might look something like this:

```rust
use modality_probe::Probe;

const REPORT_SIZE: usize = 1024;
const MOD_COLLECTOR_ADDR: &'static str = "172.16.1.1:2716";

fn send_report<P: Probe>(probe: P) -> Result<(), ReportError> {
    let mut buf = [0; REPORT_SIZE];
    if let Some(bytes_written) = probe.report(&mut buf)? {
        let mut socket = UdpSocket::bind(MOD_COLLECTOR_ADDR)?;
        socket.send(&buf[..bytes_written.get()])?;
    }
    Ok(())
}
```

### Visualizing Your Data with Graphviz

Once you have a trace that you'd like to visualize, you can use the
CLI's `export` subcommand to convert a trace file, that
`session_0_log_entries.jsonl` file from the previous section, into dot
code that you can then run Graphviz's `dot` command against:

```shell
$ modality-probe export acyclic --component ./my-component --report session_0_log_entries.jsonl > trace.dot
$ dot -Tsvg trace.dot > trace.svg
```

## Running the tests

There is a top-level testing script that executes the tests from each
subcrate: [test.sh](./test.sh).

## Reading more

See each subcrate's local readme for more information.

## License

See [LICENSE](../LICENSE) for more details.

Copyright 2020 Auxon Corporation

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
