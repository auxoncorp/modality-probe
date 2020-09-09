# `modality-probe-capi`

A C API for Modality Probe.

## Overview
`modality-probe-capi` is a library with a C API that can be used to
record events into a probe’s log, share snapshots across probes,
report a probe’s log to a collector, and provide way to associate
Modality's log with your other logging infrastructure. The library is
also targeted by the code and manifest generation that the CLI does.

## Getting Started

### Dependencies
This library requires a Rust toolchain. The recommended toolchain
management system for Rust is [Rustup](https://rustup.sh).

### Building
Once Rust is installed, build the C API using cargo:

```shell
modality-probe/modality-probe-capi $ cargo build --release
```

### Cross-platform Builds

In order to build this library for platforms other than your host
system, we recommend the use of `cross`.
For more detailed information about cross-compilation for Rust, see
[cross](https://github.com/rust-embedded/cross).

First, make `RUST_TOOLCHAIN` available in the current shell for
`cross` to have access to.

```shell
modality-probe $ export RUSTUP_TOOLCHAIN=`cat modality-probe-capi/rust-toolchain`
```

Then, make sure you have an up-to-date nightly build of Rust. You'll
also want to make sure the target you intend to build for is
installed.

```shell
modality-probe $ rustup update
modality-probe $ rustup target add thumbv7em-none-eabi
```

Now you can install `cross`, and then build the library for your
target.

```shell
modality-probe $ cargo install cross --force
modality-probe $ cross build --manifest-path modality-probe-capi/Cargo.toml --target thumbv7em-none-eabi --release
```

When using `cross` for cross-compilation, the output artifacts’
locations follow the pattern `target/<target>/<build-type>`. Given the
example above, the artifacts would be placed at
`target/thumbv7em-none-eabi/release/`.

## Usage

The probe API consists of four behaviors: event recording, snapshot
production and merging, report generation, and associating a Modality
timeline with other log data (termed “now”).

### Event Recording

To record an event into a probe’s log, use one of the variants of
`MODALITY_PROBE_RECORD`. In the example below, we’ve initialized a
probe as a global variable called `g_probe`. You’ll also note that
there are a few seemingly undefined symbols: `TWISTED` and
`CONTROLLER`. These are given definitions by making use of Modality
Probe’s CLI sub-command `header-gen` which you can read more about at
its readme<!--todo link here -->. The short of it is that you’ll need
to run the header-gen tool against your codebase before it can be
compiled because the Modality Probe CLI generates the definitions to
those symbols.

```c
#include <modality/probe.h>

/* Output of the CLI's header-gen sub-command */
#include "generated_component_ids.h"

/* The probe will be given 1024 bytes of storage space to work with */
#define DEFAULT_PROBE_SIZE (1024)
static uint8_t g_probe_buffer[DEFAULT_PROBE_SIZE];

/* The probe instance, global for convenience */
static modality_probe *g_probe = MODALITY_PROBE_NULL_INITIALIZER;

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
### Interacting with Snapshots

In Modality, the probes keep track of time _logically_, this is done
by incrementing a local counter any time a probe interacts with
another probe. The events that are recorded between these interactions
are associated with that value, which then allows Modality to create a
partial order of what happened in the system by sorting the events by
what their associated clock value was. A snapshot is how these
interactions are captured. With a snapshot, a probe sends the current
value of its own clock to another probe which then _merges_ that
snapshot. When the receiving probe merges that snapshot, it does 2
things: 1. it increments its own clock and 2. it records its
neighbor's clock along with its own. This allows Modality to associate
these two values, making the inference “When my clock was 5, my
neighbor's was 7. Anything that follows from this point was _caused
by_ the events that were recorded before this exchange.”

This work best when snapshots are used in-band. That is, they’re added
onto an existing interaction as an extra few bytes that can be
unpacked on the other end and interpreted as a snapshot for the probe
on the receiving end to merge. When this occurs out of band, the
veracity of the causal relationships Modality Probe is meant to
capture erodes—the exchanges tell us only that two components are
related, but not how.

To produce a snapshot, use `modality_probe_produce_snapshot`.

``` c
modality_causal_snapshot snap;
err = modality_probe_produce_snapshot(CONTROLLER, &snap);
```

Dually, on the receiving side, use `modality_probe_merge_snapshot` to
include that snapshot into the receiving probe's timeline.

```c
err = modality_probe_merge_snapshot(ACTUATOR, &snap);
```

### Reporting

In order to assemble a unified causal history for the system being
analyzed as a whole, each probe must periodically report out what’s in
its log, i.e., the events and interactions it’s recorded. To do that,
you use the report API.

**Note:** How often a report should be generated and sent depends on
two things: 1. The number of events you're recording, and 2. how large
your probe's buffer is. If you're not reporting often enough, the
probe can run of space to store events. When this happens, the first
threshold causes the probe to discard regular recorded events _at
record time_ to save room for interactions and system events. When the
log is completely full, all recorded events and interactions are
discarded.

The report API serializes that probe’s log into the given buffer,
which you’d then send along to your collector, probably via UDP:

```c
#include <modality/probe.h>

#define REPORT_BUFFER_SIZE (1024)
static uint8_t g_report_buffer[REPORT_BUFFER_SIZE];

static int g_report_socket = -1;
static struct sockaddr_in g_collector_addr;

/* Assumes g_report_socket and g_collector_addr have already been setup */
static void send_report(void)
{
    size_t report_size;
    const size_t err = modality_probe_report(
            g_probe,
            &g_report_buffer[0],
            REPORT_BUFFER_SIZE,
            &report_size);
    assert(err == MODALITY_PROBE_ERROR_OK);

    if(report_size != 0)
    {
        const ssize_t sendto_err = sendto(
                g_report_socket,
                &g_report_buffer[0],
                report_size,
                0,
                (const struct sockaddr*) &g_collector_addr,
                sizeof(g_collector_addr));
        assert(sendto_err != -1);
    }
}
```

If a probe does not have network access but can communicate with
another probe that does, relay this buffer there and let that
network-capable component send it on to the collector.

### Integrating a Probe’s data into your existing logging (“Now”)

Modality Probe’s “now” API allows you to associate traced events with
your existing logging infrastructure by embedding a probe’s current
clock value into your log messages:

```c
#ifdef MODALITY_PROBE_MACROS_ENABLED
    modality_probe_instant now = modality_probe_now(CONTROLLER);
    LOG(
        “controller: sent a twist command, probe clock (%d, %d, %d, %d)”,
        now.clock.id,
        now.clock.epoch,
        now.clock.ticks,
        now.clock.event_count
    );
#else
    LOG(“controller: sent a twist command”);
#endif
```

Now, when using your usual methods of log analysis, you get
correspondences of what happened causally, by finding these clock
“instances” in your logs and looking them up in the Modality Probe
causal graph by feeding your collected trace
 to the CLI's `export` subcommand.

## API

See [probe.h](./include/probe.h).

## Running the tests

Use Cargo:

```shell
$ cargo test
```

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
