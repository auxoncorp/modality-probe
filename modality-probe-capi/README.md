# `modality-probe-capi`
## Overview
`modality-probe-capi` is a library with a C that can be used to record
events into a probe’s log, share log snapshots across probes, and
report a probe’s log to a collector. The library is also targeted by
the [code and manifest generation that the CLI does](link to cli).

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
system, we recommend the use of cargo-xbuild. The default usage path
for obtaining a new target's toolchain and building for likely looks
something like the following. For more detailed information about
cross-compilation for Rust, see
[xbuild](https://github.com/rust-osdev/cargo-xbuild) and
[rustc](https://github.com/japaric/rust-cross).

```shell
modality-probe/modality-probe-capi $ rustup update
modality-probe/modality-probe-capi $ cargo install cargo-xbuild --force
modality-probe/modality-probe-capi $ rustup target add thumbv7em-none-eabi
modality-probe/modality-probe-capi $ rustc -Z unstable-options --print target-spec-json --target thumbv7em-none-eabi | tee thumbv7em-none-eabi.json
modality-probe/modality-probe-capi $ cargo xbuild --target thumbv7em-none-eabi.json --release
```

When using xbuild for cross-compilation, the output artifacts’
locations follow the pattern target/<target>/<build-type>. Following
with the example above, the artifacts would be placed at
target/thumbv7em-none-eabi/release.

## Usage

The probe API consists of four behaviors: event recording, snapshot
distribution and merging, “now”, and report generation.

### Event Recording

To record an event into a probe’s log, use one of the variants of
`MODALITY_PROBE_RECORD`. In the example below, we’ve initialized a
probe as a global called `probe_g`. You’ll also note that there are a
few seemingly undefined symbols: `TWISTED` and `CONTROLLER`. These are
given definitions by making use of Modality Probe’s CLI sub-command
`header-gen` which you can read more about at its readme<!--todo link
here -->. The short of it is that you’ll need to run the header-gen
tool against your codebase before it can be compiled because Modality
Probe actually generates the definitions to those symbols.

```c
#include <modality_probe>;

#define DEFAULT_PROBE_SIZE (1024);
modality_probe * probe_g = MODALITY_PROBE_NULL_INITIALIZER;

void twist(double x, double y, double z) {
    int result = MODALITY_PROBE_RECORD(
        probe_g,
        TWISTED,
        MODALITY_TAGS("actuation"),
        "A twist command was received"
    );
// …
}

int main() {
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);

    modality_probe_error result = MODALITY_PROBE_INIT(
        destination,
        DEFAULT_PROBE_SIZE,
        CONTROLLER,
        NULL,    /* No restart tracking */
        NULL,
        &probe_g
        MODALITY_TAGS("controller"),
        "The controller"
    );
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

To produce a snapshot, use `modality_probe_snapshot`.

``` c
modality_causal_snapshot snap;
result = modality_probe_produce_snapshot(CONTROLLER, &snap);
```

Dually, on the receving side, use `modality_probe_merge_snapshot` to
include that snapshot into the receiving probe's timeline.

```c
result = modality_probe_merge_snapshot(ACTUATOR, &snap);
```

### “Now” (Integrating a Probe’s data into your existing logging)

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
causal graph produced by collecting a trace<!--TODO link to
collector--> and feeding that trace to the export command<!-- TODO
link to export command-->.

### Reporting

In order to assemble a causal history for the system being analyzed,
each probe must periodically report what’s in its log, i.e., the
events and interactions it’s recorded. To do that, use the report API:

```c
#include <modality_probe>;

#define LOG_STORAGE_SIZE (1024);

modality_probe_error make_report(uint8_t * buffer, size_t * bytes_written) {
    modality_probe_error result = modality_probe_report(
        probe_g,
        buffer,
        LOG_STORAGE_SIZE,
        bytes_written
    );
    return result;
}
```

The report API serializes that probe’s log into the given buffer,
which you’d then send along to your collector, probably via UDP.

```c
int send_modality_report() {
    uint8_t * buffer = (uint8_t*)malloc(LOG_STORAGE_SIZE);
    size_t bytes_written;
    if (make_report(buffer, &bytes_written) != 0) {
        return 1;
    }

    int sock = socket(AF_INET, SOCK_DGRAM, 0);
    struct sockaddr_in serv_addr {
        .sin_family = AF_NET;
        .sin_port = COLLECTOR_PORT;
        .sin_addr = COLLECTOR_ADDR;
    };
    connect(sock, (struct sockaddr *) &serv_addr, sizeof(serv_addr));
    send(sock, buffer, bytes_written, 0);
}
```

If a probe does not have network access but can communicate with
another probe that does, relay this buffer there and let that
network-capable component send it on to the collector.
