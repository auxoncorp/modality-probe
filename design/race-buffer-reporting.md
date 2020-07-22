# Summary
Using a RaceBuffer for compact log storage means that old items are removed when they are overwritten by new items,
not when a report is created. As a result, reports no longer need to include the whole log, meaning there can be a 
unified bulk/chunked api which always includes as much of the log as possible. In order to remedy the problem of lost 
reports causing interactions to be lost, "frontier clocks", which represent the maximum clock values at the start of 
each report will need to be tracked at each probe. Additionally, if any items are overwritten without getting reported,
that will included in the next report as an event.

# Frontier clocks
Previously, maximum observed clocks were inserted into the log after each report was created, so the log of each report 
would always start with the clock values at the beginning of the report. However, the use of a circular buffer where 
items can be missed disallows this. Instead, frontier clocks must be explicitly tracked at each probe so they can be 
copied into the start of each report. Frontier clocks are meant to represent the maximum clock values seen in the log 
before the start of a given report's log. There are 2 scenarios in which a clock in the log should be merged into the 
tracked frontier clocks for use in future reports:
1. The clock appears in a the log of report *A* (to be clear, in this case, the clock will be merged into the probe's 
   frontier clocks for use in **future** reports that occur after *A*. The frontier clocks of *A* are written before 
   the log of *A* is processed.) 
2. The clock is overwritten in the log. In this case, the clock may have already been merged into frontier clocks if it
   was contained in the log of a report, in which case merging it again will have no effect. If the clock was 
   overwritten without getting reported, then it must be merged, or the interaction will be lost.

# Unified reporting APIs
Previously, when a bulk report was created, if the entire log could not fit into the report buffer, a hard error would
be returned. However, with the use of a circular buffer, it is possible to use a buffer of any size, and simply attempt 
to fit as many entries as possible in it. 
- Error case: If the buffer is too small for any events to fit, that is, there’s room for only the header and some or 
  all of the clocks, then a “special report” is created containing the header, then a single event stating that 
  the report buffer is too small.
- Error case: If the buffer is too small for even the header to fit, it is a hard error.

# Missed items
If the RaceBuffer overwrites old items without them getting reported, they are considered to be "missed" items. These 
items always occur at the beginning of a log read. They will be reported as an internal event with a payload indicating
how many items were missed. This event will always be placed directly after the frontier clocks in the report's payload.

# Debug collector
The debug collector reads directly from each probe's log, so it must construct a report-style log to add frontier clocks
and handle missed items. Therefore, the debug collector will keep track of the frontier clocks of each probe, and will
use the same abstracted code to deal with report payload processing.