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

To accommodate this dynamic storage mechanism, we store key-value pairs.

## Local log structure
Local to each thread, a log is stored as an array of any of the following:
- A logical clock snapshot (the log must start with this entry)
- A logged event (number)
- A logical clock diff

A single chunk of memory is allocated for log storage by the host application;
we will define a compact local representation to maximize use off this buffer.

## Tracing library
We will provide a no-std compatible Rust library to locally manage the log
structure, produce and consume logical clock messages, and to manage
communication with the collector. Additional std-only features will allow
starting an independent thread to communicate with the collector.

### Coarse API
When the user integrates the tracing library, they have to:
 - Provide init stuff
 - Provide a way to move around the logical clock: get the current value, ingest
   a peer's clock
 - Log an event
 - Do collector comms

### Concurrency
Each thread has its own logical clock and local log, which it entirely owns.
Thus, data related operations (logging an event, and interacting with the
logical clock) are lock-free and do not block the calling thread. Blocking is
allowed when doing communications only.

We may provide a wrapped-version of the api which is suitable for convenient use
across threads in a single process. This would layer a process-wide mutex (or
similar) on top of the normal lock-free api.

## Collector
### Protocol
We will define a unidirectional message-based protocol for delivering log data
back to the collector. Multiple messages may be required to deliver spooled log
data - each message should fit in a standard MTU TCP packet. Each message will
be formatted to be independently usable - the first entry will be a fully
qualified logical clock.

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

## Developer tooling
### System Id Definitions
The tracing system relies on two sets of globally unique IDs: tracer ids and
event ids. While the system can work with nothing but numbers, we provide a way
to define named tracers and events via CSV files. This allows managing these
files as spreadsheets, which is handy because the events file in particular may
become quite large.

Each row defines the ID, a short name used for code generation, and a free-form
description. An example event csv definition (note that the file must start with
a header row):

```csv
id,name,description
1245,reached_waypoint,The robot reached a designated waypoint
1246,lost_network_connectivity,The network signal dropped below usable levels
```

An example tracers csv definition:
```csv
id,name,description
0,hpc,The HPC responsible for planning
1,sensor_relay,The MPU which aggregates sensor sensor readings for the HPC
```

### Code generation
`truce-header-gen` uses the `events.csv` and `tracers.csv` files to generate a C
header file containing constants for each tracer and event.


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
- What does a diff look like for an ITC?
