# schemas

Data models for `ekotrace` in-system causal snapshot distribution.

LCM is used as the the message serialization format and schema language
for snapshots, a custom binary format is used for log reporting messages.

### Log Reporting Messages

When log data is sent from tracers back to the collector,
it uses a framing header followed by a little-endian version
of the [compact in-memory representation](../ekotrace/README.md#compact-log-representation)
used by the [ekotrace client library](../). The framing header
differs based on whether the report was generated all at once, as
as [bulk report](../src/report/bulk.rs) or was split into multiple
[report chunks](../src/report/chunked.rs) for transmission.

We observe that typical log data will have sparse
logical clock snapshots, separated by large sequences of regular events. We
split the sequence on the logical clock snapshots. A *segment* begins with a
logical clock snapshot, and is then followed by a sequence of events. When
another snapshot is reached, another segment begins.
