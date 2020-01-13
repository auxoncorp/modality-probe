# truce

Causal tracing suitable for embedded use cases.

## Overview

A `no_std` Rust implementation of a causal history tracing
mechanism.

`Tracer` instances record events that occur and collaborate
to build an interpretable joint history by sharing causal summaries
with each other inside the system-under-investigation.

`Tracer`s produce rich reports that can be transmitted
for external analysis at a user-defined cadence.

The content of those [in-system summaries](schemas/in_system.lcm)
and the [reports for external analysis](schemas/log_reporting.lcm)
are defined according to a standardized protocol, but may be treated
as opaque by users.
