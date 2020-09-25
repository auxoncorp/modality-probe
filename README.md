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

### This Repository

* [C API](./modality-probe-capi): Interact with a Modality probe from C.
* [CLI](./modality-probe-cli): The CLI used for code generation for
  probes and the visualization of a trace.
* [UDP Collector](./collectors/modality-probe-udp-collector): A
  UDP-based service that collects probes' outgoing reports.
* [Debug Collector](./collectors/modality-probe-debug-collector): A
  collector that uses JTAG to retrieve data from the probes' logs.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.sh)

### Building

Once Rust is installed, build Modality Probe using Cargo:

```shell
$ git clone https://github.com/auxoncorp/modality-probe.git
$ cd modality-probe
$ cargo build --release --all
```

If you're targeting a C application, you'll also want to build
`modality-probe-capi`.

```shell
$ cd modality-probe/modality-probe-capi
$ cargo build --release
```

## Usage

In the following sections we'll be using excerpts from the
[examples](./examples/rust-example). You can actually run the complete
example using Cargo from inside that directory.

```shell
$ cd examples/rust-example
$ cargo test
```

The probe API consists of five behaviors: initialization, event
recording, snapshot production and merging, report generation, and
associating a Modality trace with other log data (termed “now”). We'll
be covering each of these individually below.

### Initializing a Probe

Step one is to initialize your probe. Modality probes are _not_
thread-safe on their own, so it is recommended that you use a new
probe for each thread.

```rust
let mut storage = [0u8; PROBE_SIZE];
let probe = try_initialize_at!(
    &mut storage,
    PRODUCER_PROBE,
    RestartCounterProvider::NoRestartTracking,
    tags!("rust-example", "measurement", "producer"),
    "Measurement producer probe"
)?;
```

### Recording Events

Step two is to start recording events. The `try_record!` callsite
takes a probe, an event _name_, a description of the event, and any
tags you want to associate with this event.

```rust
try_record!(
    probe,
    PRODUCER_STARTED,
    "Measurement producer thread started",
    tags!("producer")
)?;
```

Events can also be recorded with payloads up to 4 bytes in size.

```rust
let mut m: i8 = 1;
let delta: i8 = rng.gen_range(-1, 2);
m = m.wrapping_add(delta);

try_record_w_i8!(
    probe,
    PRODUCER_MEASUREMENT_SAMPLED,
    m,
    tags!("producer", "measurement sample"),
    "Measurement producer sampled a value for transmission"
)?;
```

### Recording Expectations

Expectations are special events that get tagged as expectations and
also include a binary payload denoting whether or not the expectation
passed or failed.

```rust
try_expect!(
    probe,
    PRODUCER_TX_STATUS_OK,
    tx_status.is_ok(),
    "Measurement producer send result status",
    tags!("producer", "SEVERITY_10")
)?;
```

### Tracking Interactions
To connect two probe's causal history, they must exchange
_snapshots_. A snapshot contains the sender's current logical clock
and it can be merged into the receiver's log, creating a causal
relationship between the two probes.

To produce a snapshot, use `produce_snapshot`:

```rust
let snapshot = probe.produce_snapshot();
let measurement = Measurement { m, snapshot };
tx.send(measurement);
```

It should then be sent in-band if possible to the receiver. When
snapshots are sent out of band, the veracity of the causal
relationships Modality Probe is meant to capture erodes—the exchanges
tell us only that two components are related, but not necessarily how.

To merge an incoming snapshot use `merge_snapshot`.

```rust
probe.merge_snapshot(&measurement.snapshot)?;
```

### Generating Manifests & Headers

In the samples above, a macro is used to initialize a probe and to
record events. Modality Probe's CLI has a subcommand that explores
your code base for uses of these macros and turns those uses into what
Modality calls a Component. A component has a name of its own, a list
of probes (`probes.csv`), and a list of events (`events.csv`). Altogether,
a component looks like this:

```shell
$ tree my-component
├── Component.toml
├── events.csv
└── probes.csv
```

First, install the cli and then use `manifest-gen` to do this.

``` shell
$ cd modality-probe-cli
$ cargo install --path .
$ cd ../
$ modality-probe manifest-gen \
    --lang rust \
    --file-extension rs \
    --component-name example-component \
    --output-path example-component \
    examples/rust-example
```

Next, we'll want to generate the source code that gives those symbols
we discussed in the code snippet examples in the previous section
their definitions. To do that, we'll use `header-gen`:

```shell
$ modality-probe header-gen \
    --lang rust
    --output-path examples/rust-example/src/component_definitions.rs
    example-component
```

You could also include this process in your `build.rs` file
using the CLI's library interface.

```rust
use modality_probe_cli::{header_gen, lang::Lang, manifest_gen};

fn main() {
    // Use the CLI to generate component manifests
    let manifest_gen_opts = manifest_gen::ManifestGen {
        lang: Some(Lang::Rust),
        component_name: "example-component".into(),
        output_path: "example-component".into(),
        source_path: "src".into(),
        ..Default::default()
    };
    manifest_gen::run(manifest_gen_opts, None);

    // Use the CLI to generate Rust definitions from the component manifests
    let header_gen_opts = header_gen::HeaderGen {
        lang: Lang::Rust,
        output_path: Some("src/component_definitions.rs".into()),
        component_path: "example-component".into(),
        ..Default::default()
    };
    header_gen::run(header_gen_opts, None);
}
```

### Setting up a Collector

Modality Probe also ships with [a service that can collect reports via
UDP](./collectors/modality-probe-udp-collector) the reports you
generate from your probes. It writes those incoming reports as JSON
lines to a file. Start it like so:

```
$ cd collectors/modality-probe-udp-collector
$ cargo install --path .
$ cd ../../
$ modality-probe-udp-collector
Using the configuration:
    addr: 0.0.0.0:2718
    session id: 0
    output file: /home/me/src/modality-probe/session_0_log_entries.jsonl
```

When the service starts it prints the configuration it's using. In the
example above it's using all defaults. You can also pass args to
direct it to a certain port, or a specific output file.

To get data out to a collector, use the Probe's `report` API, and then
send the report that that API creates along to your collector.

```rust
fn send_report<'a>(socket: &UdpSocket, probe: &mut ModalityProbe<'a>, report_buffer: &mut [u8]) {
    let n_report_bytes = probe
        .report(report_buffer)
        .expect("Could not produce a report");
    if let Some(nonzero_report_size) = n_report_bytes {
        socket
            .send_to(&report_buffer[..nonzero_report_size.get()], COLLECTOR_ADDR)
            .expect("Could not send_to");
    }
}
```

### Running the Instrumented Example

In one terminal, run the UDP collector.

```shell
$ modality-probe-udp-collector
Using the configuration:
    addr: 0.0.0.0:2718
    session id: 0
    output file: /home/me/src/modality-probe/session_0_log_entries.jsonl
```

Then, in another terminal, navigate to the Rust example and run it.

```shell
$ cd examples/rust-examples
$ cargo run
    Finished dev [unoptimized + debuginfo] target(s) in 0.01s
     Running `target/debug/rust-example`
[2020-09-14T15:07:27Z INFO  rust_example] Modality probe reports will be sent to 127.0.0.1:2718
[2020-09-14T15:07:27Z INFO  rust_example] Sensor measurement producer thread starting
[2020-09-14T15:07:27Z INFO  rust_example] Sensor measurement consumer thread starting
[2020-09-14T15:07:27Z INFO  rust_example] Consumer recvd 2
[2020-09-14T15:07:27Z INFO  rust_example] All done
```

The `/home/me/src/modality-probe/session_0_log_entries.jsonl` file,
which is in the working directory of where you ran the collector,
should have been created with content that looks like something like
this:

```shell
$ head session_0_log_entries.jsonl
{"session_id":1,"sequence_number":0,"sequence_index":0,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"FrontierClock":{"id":518608598,"epoch":0,"ticks":0}},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":1,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"Event":1073741817},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":2,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"Event":1},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":3,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"EventWithPayload":[2,1]},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":4,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"TraceClock":{"id":518608598,"epoch":1,"ticks":1}},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":5,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"EventWithPayload":[3,1]},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":6,"probe_id":518608598,"persistent_epoch_counting":false,"data":{"Event":4},"receive_time":"2020-09-14T15:08:56.214254306Z"}
{"session_id":1,"sequence_number":0,"sequence_index":0,"probe_id":606771187,"persistent_epoch_counting":false,"data":{"FrontierClock":{"id":606771187,"epoch":0,"ticks":0}},"receive_time":"2020-09-14T15:08:56.215111896Z"}
{"session_id":1,"sequence_number":0,"sequence_index":1,"probe_id":606771187,"persistent_epoch_counting":false,"data":{"Event":1073741817},"receive_time":"2020-09-14T15:08:56.215111896Z"}
{"session_id":1,"sequence_number":0,"sequence_index":2,"probe_id":606771187,"persistent_epoch_counting":false,"data":{"Event":5},"receive_time":"2020-09-14T15:08:56.215111896Z"}
```

### Visualizing the Trace
Now we can use this collected trace and visualize it as a graph with `modality-probe export`:

```shell
$ modality-probe export acyclic --component ./example-component --report session_0_log_entries.jsonl > trace.dot
$ dot -Tpng trace.dot > trace.png
```

You can then open `trace.png` and see something like this:

![trace](https://user-images.githubusercontent.com/1194436/92818571-b6683b80-f37c-11ea-9f50-aa1fd2fbf430.png)

### Associating Causality with your Existing Logging

A Modality probe's timeline can be integrated with your existing
logging infrastructure by providing a logical sense of `now` according
to the probe's clock. This can then be included in your logging as a
breadcrumb for finding a specific event in a trace. That might look
something like this:

```rust
let instant = probe.now();
trace!("Producer now {:?}", instant);
```

## Running the tests

There is a top-level testing script that executes the tests for each
subcrate: [test.sh](./test.sh). Before you can run it, you'll need to
install the `thumbv7em-none-eabihf` target.

```shell
$ rustup target add thumbv7em-none-eabihf
$ ./test.sh
```

## License

See [LICENSE](./LICENSE) for more details.

Copyright 2020 Auxon Corporation

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

[http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0)

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
