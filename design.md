# Summary
We're making a tracing library. 

# Motivation
People will pay attention to us because this is cool and useful and open source.
Also, we need this in order to build fault injection.

# Technical Strategy
## Overview
Log events are represented by numbers, and are non-parameterized. A process uses
the trace library to produce log events. It also uses the trace library to
produce and interpret logical clock messages that are sent to collaborating
processes as a causality tracking mechanism. The library stores a sequence of
events and logical clock snapshots; a separate process sends the locally stored
events to the collector.

When a system cannot directly connect back to a collector, it may instead
communicate with a proxy running on a machine it can connect to.

## Logical Clock: ITC
We will use Interval Tree Clocks. Each 'event' in the ITC corresponds to a
single process; it increments the event counter each time the clock is sent to a
collaborating process, and each time a clock message is received.

The ITC is initially laid out (pre-forked) by the collector, to allocate an
interval to each process that can communicate with it directly. When a process
first sends its clock to a new process which does not currently own a clock
interval, it splits its own interval to transfer ownership of a subset to the
other process.

## Local log structure
Local to each process, a log is stored as an array of any of the following:
- A logical clock snapshot (the log must start with this entry)
- A logged event (number)
- A logical clock diff

A single chunk of memory is allocated for log storage by the host application;
we will define a compact binary representation to maximize use off this buffer.

TODO locking? Can we optimistically write and then CAS a length field? Can we
somehow partition this, so we have an atomic handoff to a collector thread, but
it's lock-free otherwise?

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
 - Stand up the collector thread
 - Call the log fn

## Collector
We will provide a collector deamon which runs on a regular computer, and stores
event logs into a trace corpus. It receives incremental collections of log
events via a TCP-based network interface.

## Proxy
We will provide a library which supports implementing a collector proxy; the
transport to the proxy is expected to be application specific.

# Alternatives
## Causality tracking
- Put the events in the causal context (too much data)
- Bloom clock (too new)
- DVVSets (for storage, not events)

## Log structure
We considered storing event multisets, instead of discrete events. We backed off
because it seems like a premature optimization. We may want to revisit this in
the future, as multisets degrade much more gracefully in the face of high
frequency events. We would additionally supply a threshold, beyond which a
saturation value would be stored for any given entry in the multiset.

# Costs
...

# Open Questions
- What does a diff look like for an ITC?
