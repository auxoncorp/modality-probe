# ekotrace-udp-collector

CLI-driven process that receives [ekotrace reports](../schemas/log_reporting.lcm)
over UDP and logs them to a file, per the `ekotrace-analysis` defined
[file format](../ekotrace-analysis/README.md#file-format).

## Usage

Building or installing requires a stable Rust toolchain.

### Install and run from remote

Install and run from any directory. Runs with default configuration
if no arguments are provided. 
```shell script
cargo install --git https://github.com/auxoncorp/ekotrace.git ekotrace-udp-collector
ekotrace-udp-collector-cli
```

### Build Locally

From the current directory, demonstrating the use of the `--help` option
```shell script
cargo build --release
../target/release/ekotrace-udp-collector-cli --help
```

### Build and Run in Debug Mode

From the current directory:
```shell script
cargo run -- --help
```

### CLI Options

The user may optionally supply command line arguments to specify:
* **--output-file** a path to the CSV file where the data will be logged.
Does not have to exist prior to the invocation of this command.
* **--port**  the port the server is listening on
* **--session-id**  a session id to distinguish the trace data
collected during this tracing run

## Library

This tool is also available as a Rust library, `ekotrace-udp-collector`,
for use in integration testing.
