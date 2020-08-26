# modality-probe-udp-collector

## Overview
Collect the outgoing probe reports and persist them.

## Getting Started
### Dependencies
The collector requires a Rust toolchain. The recommended toolchain
management system for Rust is [Rustup].

### Building
Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), install the CLI with Cargo

Clone this repository and use Cargo to build it locally:

```
$ git clone git@github.com:auxoncorp/modality-probe
cd modality-probe/modality-probe-udp-collector
cargo build --release
```

This will deposit a file at
`modality-probe/target/release/modality-probe-udp-collector` that can
be run directly.

## Usage

```
Server that receives modality-probe reports via UDP and logs to file

USAGE:
	modality-probe-udp-collector [OPTIONS]

FLAGS:
	-h, --help   	Prints help information
	-V, --version	Prints version information

OPTIONS:
	-o, --output-file <output-file>	Output file location
	-p, --port <port>              	What localhost port is this server going to receive data on
	-s, --session-id <session-id>  	Session id to associate with the collected trace data

```

The collector receives the reports the probes send and writes them to
the its output file.

```
$ modality-probe-udp-collector -o trace.mtr -p 9999 -s 1
```

### Sessions
A “session” is a unit used to demarcate distinct trace
collections. You may want to change the session for each test run, or
when you turn the collector off and back on again. It allows you to
compare separate traces that, without distinct session is, would
otherwise be difficult to distinguish from one another.
