# modality-probe

Embedded-friendly causal event tracing.

### Note: See [Modality Documentation](https://docs.auxon.io/modality/) for the full range of Modality's functionality.

## Overview

`modality-probe` is an open source part of [Auxon](https://auxon.io)’s [Modality](https://docs.auxon.io/modality/)
continuous verification and validation platform. Its role is to record
events and track their causal relationships between the different
parts of your system. Why? Because being able to stitch together a
causal history of a system, particularly a system _under test_,
provides a high-resolution lens into _what happened_. This history can
then be used for testing, debugging, understanding emergent scenarios,
and more.


### Environment
While `modality-probe` is written in Rust, it targets C environments,
particularly those of the embedded variety. The library used for
recording events and exchanging causality data does not depend on any
sort of standard library and is fully functional in bare-metal or RTOS
environments.

### This Repository

- [C API](./modality-probe-capi): Interact with a Modality probe from C.
- [Rust library](./src): Interact with a Modality probe from Rust.


### Open-source `modality-probe` vs. Commercial [Modality](https://docs.auxon.io/modality/)
This `modality-probe` repository represents a subset of Modality's toolset.
- Instrumentation implementation for probes and events are the same in `modality-probe` and Modality.
- `modality-probe` produces trace reports and sends them to Modality. Modality has a unified daemon which collects trace reports into a database.
- `modality-probe` raw data, whereas Modality adds advanced metrics for risk analysis and a robust trace query language.
-  Modality adds [mutators](https://docs.auxon.io/modality/reference/glossary.html#mutator), allowing you to precisely manipulate system state.


## Getting Started

### Dependencies

- [Rust Toolchain](https://rustup.rs)

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

The probe API consists of five behaviors: initialization, event
recording, snapshot production and merging, report generation, and
associating a Modality trace with other log data (termed “now”). We'll
be covering each of these individually below.

### Initializing a Probe

Step one is to initialize your probe. Modality probes are _not_
thread-safe on their own, so it is recommended that you use a new
probe for each thread.

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

Step two is to start recording events. The `record!` callsite
takes a probe, an event _name_, a description of the event, and any
tags you want to associate with this event.

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

```c
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

```c
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

Probes should use a consistent monotonic clock-source for all the time-related
measurements at a given probe (don't mix and match clock-sources for a probe).

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
*snapshots*. A snapshot contains the sender's current logical clock
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

To merge an incoming snapshot use `merge_snapshot`. Snapshots should
be merged before any other message handling occurs.

```c
err = modality_probe_merge_snapshot(
        g_consumer_probe,
        &measurement.snapshot);
assert(err == MODALITY_PROBE_ERROR_OK);
```

### Getting Trace Data Out of the System

`modality-probe` is intended to be flexible in the kind of environments
that it can be deployed in. There are generally two ways to get trace data
out of the system.

The first is to use an I/O interface on your device and use the `report` API to
send data to a waiting collector, like in this UDP-oriented example below:

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

The second is to connect to your device over its JTAG/SWD debug interface using
the related capabilities from the Modality product.

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

To run the tests, use:

```shell
$ cargo test --features std
```

There is also a top-level testing script that executes the tests for each
subcrate, [test.sh](./test.sh). Before you can run it, you'll need to
install `libusb-1.0-0-dev`, or the equivalent package for your system, and
also the `thumbv7em-none-eabihf` Rust target.

```shell
$ sudo apt install libusb-1.0-0-dev
$ rustup target add thumbv7em-none-eabihf
$ ./test.sh
```

## API

See the Tracing section of the [Modality Instrumentation SDK](https://docs.auxon.io/modality/reference/c-api.html) for detailed documentation. 
Note that the Mutation section of the [Instrumentation SDK](https://docs.auxon.io/modality/reference/c-api.html) reflects functionality exclusive to commercial Modality. 

See the comments in [probe.h](./modality-probe-capi/include/probe.h) for local documentation.

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

See [LICENSE](./LICENSE) for more details.

Copyright 2020 [Auxon Corporation](https://auxon.io)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

[http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0)

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
