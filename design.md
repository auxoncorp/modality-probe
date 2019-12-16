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

## Logical Clock: ITC
We will use Interval Tree Clocks. Each 'event' in the ITC corresponds to a
single thread; it increments the event counter each time the clock is sent to a
collaborating thread, and each time a clock message is received.

When a thread first sends its clock to a new thread which does not currently own
a clock interval, it splits its own interval to transfer ownership of a subset
to the other thread.

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
We will provide a collector daemon which runs on a regular computer, and stores
event logs into a trace corpus. It receives incremental collections of log
events via a TCP-based network interface.

TODO What should this really do? It needs to be somehow useful, if we want
anybody to use this open source thing.

### Proxy library
We will provide a library which supports implementing a linux-based collector
proxy; the incoming transport to the proxy is expected to be application
specific, but the outgoing transport will connect to the Linux-based collector.

# Alternatives
## Causality tracking
- Bloom clock (too new, but maybe a fallback if ITCs don't work)
- Plain vector clocks (not desirable because of global allocation requirement, but maybe a fallback.)
- Put the events in the causal context (too much data)
- DVVSets (for storage, not events)

## Log structure
We considered storing event multisets, instead of discrete events. We backed off
because it seems like a premature optimization. We may want to revisit this in
the future, as multisets degrade much more gracefully in the face of high
frequency events. We would additionally supply a threshold, beyond which a
saturation value would be stored for any given entry in the multiset.

# Costs
1. Prototype the dynamic ITC layout mechanism; see that it actually converges.
2. Figure out how big an ITC has to get; if it's bad, start looking for alternatives
   - Does the bloom clock paper talk about this?

# Open Questions
- What does a diff look like for an ITC?
