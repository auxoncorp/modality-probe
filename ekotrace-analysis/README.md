# ekotrace-analysis

Defines a file format for serializing collected from `ekotrace` reports to disk.

Furthermore provides several examples of analysis that can be done with
such trace data.

## File Format

The file format is CSV-based and intended to be human-readable.
Trace data from multiple tracing sessions should be recordable.

See the `LogFileLine` structure in the [Rust source](src/lib.rs)
or documentation (`cargo doc --open`) for the present contents
of each log-line.
