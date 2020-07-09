# Summary
Using a RaceBuffer for compact log storage means that old items are removed when they are overwritten by new items,
not when a report is created. As a result, clocks may need to be inserted at the beginning of each report. Additionally,
reports do not necessarily need to include all new information in the log.

# Adding clocks at beginning of reports
The RaceBuffer is never "reset" between reports, so when a report is created, log items are read starting from wherever
the last report left off. This means that the section of the log being reported may not start with any clocks, start
with a partial clock sequence, or start with a sequence of "missed" items which have been overwritten by the RaceBuffer.
In all of these cases, clocks must be inserted at the beginning of the report so that the first segment of the report
has clocks. Therefore, each probe must keep track of the clock values that have been reported so they can be inserted
when necessary.

# Keeping track of clocks
Probes will need to keep track of reported clock counts, which must be done by keeping track of clock counts that have 
been seen in reports thus far. Therefore, when creating a report, a probe must know what the final clock counts at the 
end of that report are. However, it isn't possible to interpret the log starting from the end, because compact log items
with reserved bits set could be payload items or the count item of a clock. In order to ensure that clocks are interpreted
correctly, the probe must iterate through all compact log items when making a report. Previously, in situations where
log endianness and alignment were correct, a single copy of the entire slice could be employed, but this type of copy is no
longer viable.

# Bulk reports
Since the log is never reset, bulk reports do not necessarily need to include all new log items. When creating a bulk report,
an error will be returned only if there is not enough space to include the first set of clocks. After that, the probe will 
iterate through each item in its log, appending each item to the report until there is no space left in the report buffer.

# Chunked reports
Chunked reports will not be changed much, but since the probe must interpret clocks in the log instead of apathetically copying,
additional chunked report state will need to be tracked in order to ensure that clocks or payload events split between chunks
are not misinterpreted. This state will include:
- `initial_clocks_index: Option<usize>` -In the case that the probe's `reported_clocks` included at the start of the report do not
  fit in a single chunk, include the index in the probe's `reported_clocks` of next clock.
- `is_next_suffix` - True if first item in next chunk should be interpreted as a payload/clock count 
  (meaning it is not the id item of a clock), or if the given `clock_index` refers to the count item
  of the given clock instead of the id item.

# Debug collector reports
The debug collector will read each probe's RaceBuffer log, and then will create a bulk report on the collector device 
which can then be processed into a LogReport structure.
