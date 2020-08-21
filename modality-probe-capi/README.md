# `modality-probe-capi`
## Overview
`modality-probe-capi` is a linkable C library that one can use to
record events into a probe’s log, share log snapshots across probes,
and “report” a probe’s log to a collector. The library is also
targeted by the [code and manifest generation that the CLI does](link
to cli).

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
`header-gen` which you can read more about [here TODO(link)]. The
short of it is that you’ll need to run the header-gen tool against
your codebase before it can be compiled because Modality Probe
actually generates the definitions to those symbols.

```c
#define DEFAULT_PROBE_SIZE = 7000;
modality_probe * probe_g = MODALITY_PROBE_NULL_INITIALIZER;

void twist(double x, double y, double z) {
    int result = MODALITY_PROBE_RECORD(
        probe_g,
        TWISTED,
        "tags=actuation",
        "A twist command was received"
    );
// …
}

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
### Interacting with Snapshots

For Modality Probe to do its best work regarding tracking causal
relationships between components in your system, it needs to be
included in those component’s interactions. The probes in your system
derive those relationships by exchanging “points in time” from their
own logical clocks. It’s through the snapshot API that this exchange
happens in practice.

``` c
modality_causal_snapshot snap;
result = modality_probe_produce_snapshot(CONTROLLER, &snap);
```

A snapshot can then be merged into another probe’s log with `merge`:

```c
result = modality_probe_merge_snapshot(ACTUATOR, &snap);
```

These things work best when they’re used in-band. That is, they’re
tacked onto an existing interaction as an extra few bytes that can be
unpacked on the other end and interpreted as a snapshot that the
receiving probe can merge into its probe. When these things occur out
of band, the veracity of the causal relationships Modality Probe is
meant to capture erodes—the exchanges tell us only that two components
are related, but not how they are.

### “Now” (Integrating a Probe’s data into your existing logging)

Modality Probe’s “now” API allows one to associate traced events with
your existing logging infrastructure by embedding a probe’s current
clock value into your log messages:

```c
#ifdef MODALITY_PROBE_MACROS_ENABLED
    modality_probe_instant now = modality_probe_now(CONTROLLER);
    LOG(
        “controller: sent a twist command, probe clock (%d, %d)”,
        now.clock.id,
        now.clock.count
    );
#else
    LOG(“controller: sent a twist command”);
#endif
```

Now, when using your usual methods of log analysis, you get
correspondences of what happened causally, by finding these clock
“instances” in your logs and looking them up in the Modality Probe
causal graph produced by [collecting a trace TODO link to collector]
and feeding that trace to the [export command TODO link to export command].

### Reporting

In order assemble a causal history for the system being analyzed, each
agent must periodically “report” what’s in its log, i.e., the events
and interactions it’s recorded. To do that, use the report API:

```c
uint8_t * log_storage = (uint8_t*)malloc(LOG_STORAGE_SIZE);
size_t bytes_written;
result = modality_probe_report(
    probe_g,
    log_storage,
    lOG_STORAGE_SIZE,
    &bytes_written
);
```

The report API serializes that probe’s log into the given buffer,
which you’d then send along to your collector, probably via UDP.

```c
int sock = socket(AF_INET, SOCK_DGRAM, 0);
struct sockaddr_in serv_addr {
    .sin_family = AF_NET;
    .sin_port = COLLECTOR_PORT;
    .sin_addr = COLLECTOR_ADDR;
};
connect(sock, (struct sockaddr *) &serv_addr, sizeof(serv_addr));
send(sock, log_storage, bytes_written, 0);
```

If a probe’s component does not have network access but communicates
with another component that does, relay this buffer there and let that
network-capable component send it on to the collector.
