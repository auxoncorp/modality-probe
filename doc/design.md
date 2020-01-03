# Summary
We're making a causal tracing library.

# Motivation
People will pay attention to us because this is cool and useful and open source.
Also, we need this in order to build fault injection.

# Technical Strategy
## Overview
Log events are represented by numbers, and are non-parameterized. A thread uses
the trace library to produce log events. It also uses the trace library to
produce and interpret logical clock messages that are sent to collaborating
threads (in the local process, or others) as a causality tracking mechanism. The
library stores a sequence of events and logical clock snapshots; a separate
thread sends the locally stored events to the collector.

We call each of these serial event streams a "tracer", and each one gets a
system-wide unique id.

When a system cannot directly connect back to a collector, it may instead
communicate with a proxy running on a machine it can connect to.

## Logical Clock: Neighborhood Vector Clocks
At the system level, we represent causality using a vector clock. Each 'event',
or slot in the vector clock, corresponds to one thread in the system. The thread
increments its slot in the vector clock whenever a message is sent to or
received from another thread.

Sending the entire vector clock around the system scales poorly as the number of
threads in the system increases. To mitigate this, each thread tracks the ids of
threads with which it has directly collaborated, for causality purposes (those
that sent it a logical clock). It uses this to limit the scope of the vector
clock recorded in the event log; it only records the local segment and those
from which it received logical clock messages.

To accommodate this dynamic storage mechanism, we store key-value pairs. The key
is the globally unique tracer id, and is logically a 31 bit unsigned integer.
(that's not a typo, it's 31. See 'Compact log representation' below.). The value
is a 32 bit unsigned integer representing the logical clock for that tracer.

### Logical clock overflow
When incrementing the logical clock, we use a saturating addition. So once the
maximum value of 0xffffffff is reached, it doesn't move anymore. We additionally
set a boolean overflow flag, which is transimitted back to the collector.

### Logical clock transmission and encoding

When using the library, the user must share the tracer-managed logical clock
with other tracers. This should be done in-band with existing communications
channels. From the API perspective, this payload is opaque; it simply needs to
arrive at the other end intact, and be merged in to that side's tracer.

Internally, we encode this payload using LCM. In consists of the tracer's own ID
and logical clock, along with the logical clocks of each of each of its
immediate neighbors. In principle, we should be able to get away with just
transmitting the tracer's own clock, but this adds some redundancy in the case
where the sending and receiving tracers have shared neighbors.

The schema is defined in [in_system.lcm](file:../truce/schemas/in_system.lcm).

## Compact log representation
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

## Tracing library
We will provide a no-std compatible Rust library to locally manage the log
structure, produce and consume logical clock messages, and to manage
communication with the collector. Additional std-only features will allow
starting an independent thread to communicate with the collector.

### C API
While implemented in Rust, the tracing library provides a C API for easy
integration with embedded development stacks. There are three basic points of
interaction, post-initialization:

1. Event logging: `tracer_record_event` is used to add an event to the log.

2. Causality tracking: `tracer_share_history` will produce a causality payload
   which should be passed to other tracers, and `tracer_merge_history` can be
   used to consume the payload when it is received.

3. Reporting: `tracer_export_log` will fill a user-provided buffer with
   LCM-formatted log data that is ready to be transmitted to the collector.

The C API is defined in [trucec.h](file:../truce/truce-c/include/trucec.h).

### Concurrency
Each thread has its own logical clock and local log, which it entirely owns.
Thus, data related operations (logging an event, and interacting with the
logical clock) are lock-free and do not block the calling thread. Blocking is
allowed when doing communications only.

We may provide a wrapped-version of the api which is suitable for convenient use
across threads in a single process. This would layer a process-wide mutex (or
similar) on top of the normal lock-free api.

## Collector
### Log Reporting Messages
LCM is used as the the message serialization format and schema language.

When log data is sent from tracers back to the collector, it uses a slightly
different data structure. While the compact in-memory representation could be
shipped directly as a binary payload, that format cannot be represented by any
schema language we know of. Instead, we define a slightly less efficient
structure that /can/ be described by the schema, gaining the documentation and
interoperability benefits it provides.

In the transport format, we observe that typical log data will have sparse
logical clock snapshots, separated by large sequences of regular events. We
split the sequence on the logical clock snapshots. A *segment* begins with a
logical clock snapshot, and is then followed by a sequence of events. When
another snapshot is reached, another segment begins.

At the top level of the log message, we also send the source tracer id and some
top-level overflow flags.

The schema is defined in [log_reporting.lcm](file:../truce/schemas/log_reporting.lcm).

### TCP Transport
TODO Define a TCP-based transport for this.


### Linux-based daemon
We will provide a collector daemon which runs on a regular computer. It receives
incremental collections of log events via a TCP-based network interface. It
stores this information in a plain-text file.

### Basic CLI tooling
We will provide some kind of primitive command line tooling.

- Interpret an event id -> name map

- View log events

- Basic filtering

- Some kind of interpretation of the causal relationships between events.

  - Perhaps a textual sequence diagram

### Proxy library
We will provide a library which supports implementing a Linux-based collector
proxy; the incoming transport to the proxy is expected to be application
specific, but the outgoing transport will connect to the Linux-based collector.

# Alternatives
## Causality tracking
- Bloom clock (too new, but maybe a fallback if ITCs don't work)
- Plain vector clocks (not desirable because of global allocation requirement, but maybe a fallback.)
- Put the events in the causal context (too much data)
- DVVSets (for storage, not events)
- ITC won't work, as it can't handle multiple roots.

## Log structure
We considered storing event multisets, instead of discrete events. We backed off
because it seems like a premature optimization. We may want to revisit this in
the future, as multisets degrade much more gracefully in the face of high
frequency events. We would additionally supply a threshold, beyond which a
saturation value would be stored for any given entry in the multiset.

We may want to add a regular timestamp to the logical clock rows, to help
interpretability.

# Costs

# Open Questions
