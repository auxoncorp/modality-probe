# ekotrace

Causal tracing suitable for embedded use cases.

## Overview

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
let n_snapshot_bytes = ekotrace_instance_foo.distribute_snapshot(&mut snapshot_buffer).unwrap();

// ... in a different component in the system ...

// Assume the user has made the bytes written by `ekotrace_instance_foo`
//in `snapshot_buffer` available here (e.g. through messaging)
ekotrace_instance_bar.merge_snapshot(&snapshot_buffer[..n_snapshot_bytes]).unwrap();
```

Internally, we encode this payload using LCM. In consists of the tracer's own ID
and logical clock, along with the logical clocks of each of each of its
immediate neighbors. In principle, we should be able to get away with just
transmitting the tracer's own clock, but this adds some redundancy in the case
where the sending and receiving tracers have shared neighbors.

The schema is defined in [in_system.lcm](../schemas/in_system.lcm).
