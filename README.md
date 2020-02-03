# ekotrace

A distributed causal tracing system suitable for embedded use.

> **This work is currently in progress. We are planning to make
> changes and will note [here](CHANGELOG.md) when you will need
> to make an update.**

## Background

`ekotrace` tracks events of interest in a system as well as
the causal relationships of those events.

The trace data that `ekotrace` outputs shows, for example,
whether event B happened because of event A, or
whether event B happened independently of event A.

Causal tracing works without relying on system clocks at all.

`ekotrace` can trace one or many embedded components and provides
information about the impact of each component on the system as
a whole.

## Overview (TODO)

A `no_std` Rust implementation of a causal history tracing
mechanism.

`Ekotrace` instances record events that occur and collaborate
to build an interpretable joint history by sharing causal snapshots
with each other inside the system-under-investigation.

`Ekotrace`s produce rich reports that can be transmitted
for external analysis at a user-defined cadence.

The content of those [in-system summaries](../schemas/in_system.lcm)
and the [reports for external analysis](../schemas/log_reporting.lcm)
are defined according to a standardized protocol, but may be treated
as opaque by users.

## Detailed Technical Strategy

Log events are represented by numbers, and are (currently) non-parameterized.
A thread uses the [ekotrace client library](.) to produce log events.

A thread also uses this ekotrace library to produce and interpret logical clock messages
that are sent to collaborating threads (in the local process, or others) as a
causality tracking mechanism. The library stores a sequence of events and logical
clock snapshots. These locally stored events can be packaged as a report to send
to the collector.

We call a thread using the ekotrace library a "Ekotrace location", and each one gets a
system-wide unique id, referred to as a "tracer id" or "location id".

When a system cannot directly connect back to a collector, it may instead
communicate with a proxy running on a machine it can connect to.

### Logical Clock: Neighborhood Vector Clocks

At the system level, we represent causality using a vector clock. Each slot in the
vector clock, must corresponds to one thread (a.k.a. "location") in the system.
The thread increments its slot in the vector clock whenever a message is sent to or
received from another thread.

Sending the entire vector clock around the system scales poorly as the number of
threads in the system increases. To mitigate this, each thread tracks the ids of
threads from which it has directly received messages, for causality purposes (those
that sent it a logical clock). It uses this to limit the scope of the vector
clock recorded in the event log; it only records the local segment and those
from which it received logical clock messages.

To accommodate this dynamic storage mechanism, we store key-value pairs. The key
is the globally unique tracer id, and is logically a 31 bit unsigned integer.
(that's not a typo, it's 31. See 'Compact log representation' below.). The value
is a 32 bit unsigned integer representing the logical clock for that tracer.

### Compact log representation
Local to each thread, we store a compact sequence of interleaved events and
logical clock snapshots. We use a compact encoding for this:

- The log is stored as an array of 32-bit unsigned integers

- Events are stored as a single array entry, but the high bit must be zero (so
  you only get 31 bits of resolution).

- If the high bit is 1, then the remainder of the integer represents a tracer
  id. In this case, the following array entry is the value of the logical clock
  for that tracer, at this point in the log.

This data structure supports the partial storage of logical clocks, so only the
part that is changed needs to be recorded.

Future versions of this data structure may use a variable-length integer
representation (protobuf-style) for even more compact storage.

Future versions of the data structure might include a variety of
event which can be associated with a small data payload, such as
another 32 bit integer.

### Logical clock overflow
When incrementing the logical clock, we use saturating addition. So once the
maximum value of 0xffffffff is reached, it doesn't move anymore. We additionally
set a boolean overflow flag, which is transmitted back to the collector.

### Concurrency

Each thread has its own logical clock and local log, which it entirely owns,
managed by an `Ekotrace` instance.
Thus, data related operations (logging an event, and interacting with the
logical clock) are lock-free and do not block the calling thread. Blocking is
allowed when doing communications only.

In the future, we may provide a wrapped-version of the api which is suitable
for convenient use across threads in a single process. This would layer a
process-wide mutex (or similar) on top of the normal lock-free api.

### Logical clock transmission and encoding

When using the library, the user must share the tracer-managed logical clock
with other tracers. This should be done in-band with existing communications
channels. From the API perspective, this payload is opaque; it simply needs to
arrive at the other end intact, and be merged in to that side's tracer.

```rust
let mut snapshot_buffer = [0u8; 256];
let n_snapshot_bytes = ekotrace_instance_foo.distribute_snapshot(&mut snapshot_buffer)?;

// ... in a different component in the system ...

// Assume the user has made the bytes written by `ekotrace_instance_foo`
//in `snapshot_buffer` available here (e.g. through messaging)
ekotrace_instance_bar.merge_snapshot(&snapshot_buffer[..n_snapshot_bytes])?;
```

Internally, we encode this payload using LCM. In consists of the tracer's own ID
and logical clock, along with the logical clocks of each of each of its
immediate neighbors. In principle, we should be able to get away with just
transmitting the tracer's own clock, but this adds some redundancy in the case
where the sending and receiving tracers have shared neighbors.

The schema is defined in [in_system.lcm](../schemas/in_system.lcm).

## Overview (TODO)

The core of `ekotrace` is the [reference client library implementation](ekotrace),
which provides the capabilities developers need to start capturing trace
data in their systems of interest.

```rust
// Initialization of an ekotrace instance only needs to happen once
// in the lifetime of a thread / execution context
let ekotrace_foo = Ekotrace::initialize_at(&mut storage_bytes, LOCATION_ID_FOO)?;
ekotrace_foo.record_event(EVENT_A);
ekotrace_foo.record_event(EVENT_B);
```

The above demonstrates using an `ekotrace` instance to record some events. These events are
in that instance's timeline.
`ekotrace` instances identify specific points in time by making causal snapshots.

```rust
let mut snapshot_buffer = [0u8; 256];
let n_snapshot_bytes = ekotrace_foo.distribute_snapshot(&mut snapshot_buffer)?;
```

To connect the dots between the timelines of `ekotrace` instances in different locations,
distribute and merge those causal snapshots.

```rust
// ... in a different component in the system ...

// ekotrace_bar, the local ekotrace instance, would have been created
// at the start of this process / thread
let ekotrace_bar = Ekotrace::initialize_at(&mut storage_bytes, LOCATION_ID_BAR)?;

// Assume the user has made the bytes written by `ekotrace_foo` into `snapshot_buffer` available
// (e.g. through messaging)
ekotrace_bar.merge_snapshot(&snapshot_buffer[..n_snapshot_bytes])?;
// From this point on, events recorded by ekotrace_bar can be sure
// to have happened after / because of the events at ekotrace_foo at the time
// of that snapshot.
ekotrace_bar.record_event(EVENT_C);
```

The `ekotrace` client provides a system-agnostic approach to reporting. `ekotrace` instances
write their report data into a byte buffer, which can be sent to a report collecting backend
whichever way the system under test prefers. Report content can be treated as opaque
bytes by the embedded system.

```rust
let mut report_buffer = [0u8; 1024];
let n_report_bytes = ekotrace.report(&mut report_buffer)?;
send_bytes(&report_buffer[..n_report_bytes]); // send_bytes is user-defined
```

The [ekotrace-udp-collector](ekotrace-udp-collector) is a reference implementation of a
trace data logging backend. It uses UDP to receive `ekotrace` report bytes from the client
(bytes which conform to a [standardized schema](schemas/log_reporting.lcm)) and logs
trace data to a file for offline analysis.

## Id Management

`ekotrace` requires the user to provide a unique id for each distinct location (read: execution context) of interest
in the system. Practically speaking, this means one tracer-location id per thread. In order to
help coordinate id management, an optional [id definition file format](ekotrace-header-gen/README.md#id-management-format) is defined.

`ekotrace` also requires the user to provide unique ids for the events they care about, which may
be managed in a similar fashion as tracer ids.

Event and tracer ids can be automatically generated for a project that uses the `ekotrace` API
with the [ekotrace-manifest-gen](ekotrace-manifest-gen) tool.

The [ekotrace-header-gen](ekotrace-header-gen) tool automates away id-in-code definition effort.

## APIs

The client library has a [C API](ekotrace-capi) and a `no_std` no-alloc compatible [Rust API](ekotrace) available.

See the [C API README](ekotrace-capi/README.md) for directions on using
`ekotrace` from C as a static library.

## Automated Workflow Example

Start using the `ekotrace` API, don't worry about defining your event identifiers.

```rust
// src/tracing_ids.rs mod generated by ekotrace-header-gen
use crate::tracing_ids::*;

// Initialization of an ekotrace instance only needs to happen once
// in the lifetime of a thread / execution context
let ekotrace_foo = Ekotrace::try_initialize_at(&mut storage_bytes, LOCATION_ID_FOO)?;

// Record events
match bar() {
    true => ekotrace_foo.record_event(EVENT_A),
    false => ekotrace_foo.record_event(EVENT_B),
}
```

Add a build script to generate the event ids and definitions.

```toml
# Cargo.toml
build = "build.rs"
```

```rust
# build.rs
use std::fs::File;
use std::io::{self, Write};
use std::process::Command;

fn main() {
    // Generate `events.csv` and `tracers.csv` id manifest files, searching in src/ directory
    let status = Command::new("ekotrace-manifest-gen")
        .arg("--events-csv-file")
        .arg("events.csv")
        .arg("--tracers-csv-file")
        .arg("tracers.csv")
        .arg("src/")
        .status()
        .expect("ekotrace-manifest-gen failed unexpectedly");
    assert!(status.success());

    // Generate Rust definitions for event and tracer ids in `src/tracing_ids.rs`
    let mut events_src = File::create("src/tracing_ids.rs").expect("Could not make file");
    let output = Command::new("ekotrace-header-gen")
        .arg("--lang")
        .arg("Rust")
        .arg("events.csv")
        .arg("tracers.csv")
        .output()
        .expect("ekotrace-header-gen failed unexpectedly");
    io::stderr().write_all(&output.stderr).expect("Could not write to stderr");
    events_src.write_all(&output.stdout).expect("Could not write to stdout");
    assert!(output.status.success());
}
```

Building the project now generates `events.csv`, `tracers.csv` and `src/tracing_ids.rs`

```bash
cargo build
```

Users can further annotate the event and tracer id files with descriptions
and additional definitions.

```csv
id,name,description
1,event_a,Event A occurred
2,event_b,Event B was triggered
3,event_c,Event C for future use
3,event_d,Event D also for future use
```
