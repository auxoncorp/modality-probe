# ekotrace-analysis

## Overview

A Rust library that defines a file format for serializing collected
data from `ekotrace` reports to disk.

Furthermore provides several examples of analysis that can be done with
such trace data.

## File Format

The file format is CSV-based and intended to be human-readable.
Trace data from multiple tracing sessions should be recordable.

See the `LogFileLine` structure in the [Rust source](src/lib.rs)
or documentation (`cargo doc --open`) for the present contents
of each log-line.

## Getting Started

```toml
# Cargo.toml

[dependencies]
ekotrace-analysis = { git = "ssh://git@github.com/auxoncorp/ekotrace.git" }
```

## Usage

See [ekotrace-cli](../ekotrace-cli) for examples of analysis that can be done with trace data.

## License

Please see [LICENSE](../LICENSE) for more details.
