# schemas

Data models for `ekotrace` in-system causal snapshot distribution
and reporting.

LCM is used as the the message serialization format and schema language.

### Log Reporting Messages

When [log data](log_reporting.lcm) is sent from tracers back to the collector,
it uses a slightly different data structure than the [compact in-memory representation](../ekotrace/README.md#compact-log-representation)
used by the [ekotrace client library](../ekotrace). While the compact in-memory
representation could be shipped directly as a binary payload, that format
cannot easily be represented by any schema language we know of associated
with a reasonably efficient serialization approach.
Instead, we define a slightly less efficient structure that *can* be described
by the schema, gaining the documentation and interoperability benefits LCM
provides.

In the transport format, we observe that typical log data will have sparse
logical clock snapshots, separated by large sequences of regular events. We
split the sequence on the logical clock snapshots. A *segment* begins with a
logical clock snapshot, and is then followed by a sequence of events. When
another snapshot is reached, another segment begins.

At the top level of the log message, we also send the source tracer id and some
top-level overflow flags.
