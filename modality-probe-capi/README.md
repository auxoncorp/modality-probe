# modality-probe-capi

A C API for Modality Probe.

## Overview
`modality-probe-capi` is a library with a C API that can be used to
record events into a probe’s log, share snapshots across probes,
report a probe’s log to a collector, and provide way to associate
Modality's log with your other logging infrastructure. The library is
also targeted by the code and manifest generation that the CLI does.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.rs)

### Building
Once Rust is installed, build the C API using Cargo:

```shell
$ git clone https://github.com/auxoncorp/modality-probe.git
$ cd modality-probe/modality-probe-capi
$ cargo build --release
```

### Cross-platform Builds

In order to build this library for platforms other than your host
system, we recommend the use of `cross`.
For more detailed information about cross-compilation for Rust, see
[cross](https://github.com/rust-embedded/cross).

First, make `RUST_TOOLCHAIN` available in the current shell for
`cross` to have access to.

```shell
$ visualize RUSTUP_TOOLCHAIN=`cat modality-probe-capi/rust-toolchain`
```

Then, make sure you have an up-to-date nightly build of Rust. You'll
also want to make sure the target you intend to build for is
installed.

```shell
$ rustup update
$ rustup target add thumbv7em-none-eabi
```

Now you can install `cross`, and then build the library for your
target.

```shell
$ cargo install cross --force
$ cross build --manifest-path modality-probe-capi/Cargo.toml --target thumbv7em-none-eabi --release
```

When using `cross` for cross-compilation, the output artifacts’
locations follow the pattern `target/<target>/<build-type>`. Given the
example above, the artifacts would be placed at
`target/thumbv7em-none-eabi/release/`.

## Usage

In the following sections we'll be using excerpts from the
[examples](/examples/c-example). You can actually run the complete
example using Cargo from inside that directory.

```shell
$ cd ../examples/c-example
$ make test
```

The probe API consists of five behaviors: initialization, event
recording, snapshot production and merging, report generation, and
associating a Modality trace with other log data (termed “now”). We'll
be covering each of these individually below.

### Initializing a Probe

Step one is to initialize your probe. Modality probes are _not_
thread-safe on their own, so it is recommended that you use a new
probe for each thread or execution context.

```c
err = MODALITY_PROBE_INIT(
        &g_producer_probe_buffer[0],
        sizeof(g_producer_probe_buffer),
        PRODUCER_PROBE,
        MODALITY_PROBE_TIME_RESOLUTION_UNSPECIFIED,
        MODALITY_PROBE_WALL_CLOCK_ID_LOCAL_ONLY,
        NULL,
        NULL,
        &g_producer_probe,
        MODALITY_TAGS("c-example", "measurement", "producer"),
        "Measurement producer probe");
assert(err == MODALITY_PROBE_ERROR_OK);
```

### Recording Events

Step two is to start recording events. The `MODALITY_PROBE_RECORD`
callsite takes a probe, an event _name_, a description of the event,
and any tags you want to associate with this event.

```c
err = MODALITY_PROBE_RECORD(
        g_producer_probe,
        PRODUCER_STARTED,
        MODALITY_TAGS("producer"),
        "Measurement producer started");
assert(err == MODALITY_PROBE_ERROR_OK);
```

Events can also be recorded with payloads up to 4 bytes in size.

```c
const int8_t sample = g_producer_measurement.m + (int8_t) (-1 + (rand() % 4));

err = MODALITY_PROBE_RECORD_W_I8(
        g_producer_probe,
        PRODUCER_MEASUREMENT_SAMPLED,
        sample,
        MODALITY_TAGS("producer", "measurement sample"),
        "Measurement producer sampled a value for transmission");
assert(err == MODALITY_PROBE_ERROR_OK);
```

### Recording Expectations

Expectations are special events that get tagged as expectations and
also include a binary payload denoting whether or not the expectation
passed or failed.

```rust
err = MODALITY_PROBE_EXPECT(
        g_producer_probe,
        PRODUCER_SAMPLE_DELTA_OK,
        (sample - g_producer_measurement.m) <= 2,
        MODALITY_TAGS("producer"),
        MODALITY_SEVERITY(10),
        "Measurement delta within ok range");
```

### Recording Failures

Failures are special events that get tagged as failures to
denote "something bad happened".

```rust
err = MODALITY_PROBE_FAILURE(
        g_producer_probe,
        BAD_THING_HAPPENED,
        MODALITY_TAGS("problem"),
        MODALITY_SEVERITY(5),
        "A bad thing happened");
```

### Recording Wall Clock Time

Wall clock time can be recorded as a standalone timestamp or
alongside other events.

A probe that uses wall clock time can identify the time domain it's operating
in via a `WallClockId`. All probes in the same time domain should
use the same wall clock identifier.

Probes should use a consistent monotonic clock-source for all the time-related measurements
at a given probe (don't mix and match clock-sources for a probe).

```c
uint64_t time_ns = 1;

err = modality_probe_record_time(probe, time_ns);
assert(err == MODALITY_PROBE_ERROR_OK);

err = MODALITY_PROBE_RECORD_W_TIME(
        g_producer_probe,
        PRODUCER_STARTED,
        time_ns,
        MODALITY_TAGS("producer"),
        "Measurement producer started");
assert(err == MODALITY_PROBE_ERROR_OK);

err = MODALITY_PROBE_RECORD_W_I8_W_TIME(
        g_producer_probe,
        PRODUCER_MEASUREMENT_SAMPLED,
        sample,
        time_ns,
        MODALITY_TAGS("producer", "measurement sample"),
        "Measurement producer sampled a value for transmission");
assert(err == MODALITY_PROBE_ERROR_OK);
```

### Tracking Interactions

To connect two probe's causal history, they must exchange
_snapshots_. A snapshot contains the sender's current logical clock
and it can be merged into the receiver's log, creating a causal
relationship between the two probes.

To produce a snapshot, use `produce_snapshot`:

```c
err = modality_probe_produce_snapshot(
        g_producer_probe,
        &g_producer_measurement.snapshot);
```

It should then be sent in-band if possible to the receiver. When
snapshots are sent out of band, the veracity of the causal
relationships Modality Probe is meant to capture erodes—the exchanges
tell us only that two components are related, but not necessarily how.

To merge an incoming snapshot use `merge_snapshot`.

```c
err = modality_probe_merge_snapshot(
        g_consumer_probe,
        &measurement.snapshot);
assert(err == MODALITY_PROBE_ERROR_OK);
```

### Generating Manifests and Headers

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
$ cd ../modality-probe-cli
$ cargo install --path .
$ cd ../modality-probe-capi
$ modality-probe manifest-gen \
    --lang c \
    --file-extension c \
    --component-name example-component \
    --output-path example-component \
    examples/c-example
```

Next, we'll want to generate the source code that gives those symbols
we discussed in the code snippet examples in the previous section
their definitions. To do that, we'll use `header-gen`:

```shell
$ modality-probe header-gen \
    --lang c \
    --output-path examples/c-example/include/component_definitions.h \
    example-component
```

NOTE: It can be helpful to have the manifest and header generation tools run as
part of your regular build process to automatatically pick up changes to
your instrumentation or alert you to potential issues in your instrumentation.

### Setting up a Collector

Modality Probe also ships with [a service that can collect via
UDP](/collectors/modality-probe-udp-collector) the reports you
generate from your probes. It writes those incoming reports as JSON
lines to a file. Start it like so:

```
$ cd ../collectors/modality-probe-udp-collector
$ cargo install --path .
$ cd ../../modality-probe-capi
$ modality-probe-udp-collector
Using the configuration:
    addr: 0.0.0.0:2718
    session id: 0
    output file: /home/me/src/modality-probe/modality-probe-capi/session_0_log_entries.jsonl
```

When the service starts it prints the configuration it's using. In the
example above it's using all defaults. You can also pass CLI arguments to
direct the collector to listen on a certain port and write to a specific
output file. Check `modality-probe-udp-collector --help` for details.

### Getting Trace Data Out of the System

`modality-probe` is intended to be flexible in the kind of environments
that it can be deployed in. There are generally two ways to get trace data
out of the system.

The first is to use an I/O interface on your device and use the `report` API to
send data to a waiting collector, like in this UDP oriented example below:

```c
static void send_report(modality_probe * const probe)
{
    size_t report_size;
    const size_t err = modality_probe_report(
            probe,
            &g_report_buffer[0],
            sizeof(g_report_buffer),
            &report_size);
    assert(err == MODALITY_PROBE_ERROR_OK);

    if(report_size != 0)
    {
        const ssize_t status = sendto(
                g_report_socket,
                &g_report_buffer[0],
                report_size,
                0,
                (const struct sockaddr*) &g_collector_addr,
                sizeof(g_collector_addr));
        assert(status != -1);
    }
}
```

The second is to connect to your device over its JTAG/SWD debug interface using the
`modality-probe-debug-collector` and pull data down over the debug interface to
the host machine ([see here for details](./collectors/modality-probe-debug-collector/README.md)).

### Running the Instrumented Example

In one terminal, run the UDP collector.

```shell
$ modality-probe-udp-collector
Using the configuration:
    addr: 0.0.0.0:2718
    session id: 0
    output file: /home/me/src/modality-probe/modality-probe-capi/session_0_log_entries.jsonl
```

Then, in another terminal, navigate to the C example and run it.

```shell
$ cd ../examples/c-examples
$ make run
Modality probe reports will be sent to 127.0.0.1:2718
Sensor measurement producer starting
Sensor measurement consumer starting
Consumer recvd -1
Shutting down
All done
```

The `/home/me/src/modality-probe/modality-probe-capi/session_0_log_entries.jsonl` file,
which is in the working directory of where you ran the collector,
should have been created with content that looks like something like
this:

```shell
$ head session_0_log_entries.jsonl
{"session_id":1,"sequence_number":0,"sequence_index":0,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"FrontierClock":{"id":697885215,"epoch":0,"ticks":0}},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":1,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"Event":1073741817},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":2,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"Event":1},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":3,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"EventWithPayload":[3,1]},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":4,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"TraceClock":{"id":697885215,"epoch":1,"ticks":1}},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":5,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"EventWithPayload":[4,1]},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":6,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"Event":5},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":7,"probe_id":697885215,"persistent_epoch_counting":false,"data":{"Event":2},"receive_time":"2020-09-14T15:10:35.938584823Z"}
{"session_id":1,"sequence_number":0,"sequence_index":0,"probe_id":354168348,"persistent_epoch_counting":false,"data":{"FrontierClock":{"id":354168348,"epoch":0,"ticks":0}},"receive_time":"2020-09-14T15:10:35.939494439Z"}
{"session_id":1,"sequence_number":0,"sequence_index":1,"probe_id":354168348,"persistent_epoch_counting":false,"data":{"Event":1073741817},"receive_time":"2020-09-14T15:10:35.939494439Z"}
```

### Inspecting a Trace from Your Terminal

The Modality Probe CLI also provides a way to inspect a trace from
your terminal with the `log` subcommand. Given the trace we generated
in the “Running the Instrumented Example” section above, we can
inspect that trace with the following command:

```shell
$ modality-probe log -vv --component-path ./example-component --report session_0_log_entries.jsonl
```

This command takes a path to the component's metadata and a path to
the trace; it also asks `log` to provide its most verbose output
(`-vv`). That output should look something like this:

```
Clock Tick @ CONSUMER_PROBE (1:30020207:0:1) clock=(0, 0)

CONSUMER_STARTED @ CONSUMER_PROBE (1:30020207:0:3)
    description: "Measurement consumer thread started"
    payload: None
    tags: consumer
    event source: "c-example/src/main.rs#L196"
    probe tags: c-example, measurement, consumer
    probe source: "c-example/src/main.rs#L186"
    component: example-component

Clock Tick @ PRODUCER_PROBE (1:837318897:0:1) clock=(0, 0)

PRODUCER_STARTED @ PRODUCER_PROBE (1:837318897:0:3)
    description: "Measurement producer thread started"
    payload: None
    tags: producer
    event source: "c-example/src/main.rs#L102"
    probe tags: c-example, measurement, producer
    probe source: "c-example/src/main.rs#L92"
    component: example-component
```

Alternatively, you can pass `--graph` to `log` and it will _graph_ the
interactions and events across all of the probes. It should look
something like this:

```
*   |   CONSUMER_STARTED @ CONSUMER_PROBE (1:30020207:0:3)
|   |       description: "Measurement consumer thread started"
|   |       tags: consumer
|   |       event source: "c-example/src/main.rs#L196"
|   |       probe tags: c-example, measurement, consumer
|   |       probe source: "c-example/src/main.rs#L186"
|   |       component: example-component
|   |
|   *   PRODUCER_STARTED @ PRODUCER_PROBE (1:837318897:0:3)
|   |       description: "Measurement producer thread started"
|   |       tags: producer
|   |       event source: "c-example/src/main.rs#L102"
|   |       probe tags: c-example, measurement, producer
|   |       probe source: "c-example/src/main.rs#L92"
|   |       component: example-component
|   |
|   *   PRODUCER_MEASUREMENT_SAMPLED @ PRODUCER_PROBE (1:837318897:0:4)
|   |       description: "Measurement producer sampled a value for transmission"
|   |       payload: 1
|   |       tags: producer, measurement sample
|   |       event source: "c-example/src/main.rs#L144"
|   |       probe tags: c-example, measurement, producer
|   |       probe source: "c-example/src/main.rs#L92"
|   |       component: example-component
|   |
+<--+   CONSUMER_PROBE merged a snapshot from PRODUCER_PROBE
```

### Visualizing the Trace

Now we can use this collected trace and visualize it as a graph with
`modality-probe visualize` which will export the trace as a Graphviz
DOT format file. The example below uses the `dot` command, and thus
assumes you've already installed Graphviz which includes `dot`:

```shell
$ modality-probe visualize acyclic --component-path ./example-component --report session_0_log_entries.jsonl > trace.dot
$ dot -Tpng trace.dot > trace.png
```

You can then open `trace.png` and see something like this:

![trace](https://user-images.githubusercontent.com/1194436/95799022-4402b800-0ca8-11eb-9ad3-a8c0fab31fe5.png)

### Associating Causality with your Existing Logging

A Modality probe's timeline can be integrated with your existing
logging infrastructure by providing a logical sense of `now` according
to the probe's clock. This can then be included in your logging as a
breadcrumb for finding a specific event in a trace. That might look
something like this:

```c
const modality_probe_instant now = modality_probe_now(g_producer_probe);
syslog(
        LOG_INFO,
        "Producer now "
        "(id: %" PRIu32 ", epoch: %" PRIu16 ", ticks: %" PRIu16 ", event_count: %" PRIu32 ")\n",
        now.clock.id,
        now.clock.epoch,
        now.clock.ticks,
        now.event_count);
```

This will place a Modality causal-coordinate into your log message, so
that later in offline processing any given log message can be
correlated with a specific location in the Modality probe's logical
timeline. You can now stitch together the causal history of your
typical device logging along side Modality's events and expectations.

## Running the Tests

To run the C API tests use:

```shell
$ cargo test
```

## API

See [probe.h](./include/probe.h) for details.

## CMake

The release package provides a find script and a set of CLI helper functions
for CMake integrations under the `cmake/` directory.

Add the following to your `CMakeLists.txt`:

```cmake
list(APPEND CMAKE_MODULE_PATH "/path/to/modality-probe/cmake")

# Provides ModalityProbe::LibModalityProbe target
find_package(ModalityProbe REQUIRED)

# Provides CLI invocation targets
include(ModalityProbeCli)

modality_probe_generate_manifest(
    TARGET example
    DEPENDS src/main.c
    COMPONENT_NAME "example-component"
    OUTPUT_PATH "example-component"
    EXCLUDES "build/"
    FILE_EXTENSIONS "c" "cpp"
    SOURCE_PATH ".")

modality_probe_generate_header(
    TARGET example
    OUTPUT_FILE "include/component_definitions.h"
    COMPONENT_PATH "example-component")

target_link_libraries(example PRIVATE ModalityProbe::LibModalityProbe)
```

## License

See [LICENSE](../LICENSE) for more details.

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
