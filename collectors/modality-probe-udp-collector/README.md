# modality-probe-udp-collector

Collect the outgoing probe reports and persist them.

## Overview

The UDP collector is a service that's meant to be targeted by a
system's probes as a report collector. It serializes the incoming
reports into json lines and writes those lines to a file.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.sh)

### Building
Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), clone this repository and use Cargo to build it
locally:

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

```
$ modality-probe-udp-collector
Using the configuration:
    addr:               0.0.0.0:2718
    session id:         0
    output file:        /home/dpitt/src/modality-probe/collectors/modality-probe-udp-collector/session_0_log_entries.jsonl
```

This example uses the default configuration, but as seen above, a
port, session, and file can be given via CLI options.

## Sessions

A “session” is a unit used to demarcate distinct trace
collections. You may want to change the session for each test run, or
when you turn the collector off and back on again. It allows you to
compare separate traces that, without distinct sessions, would
otherwise be difficult to distinguish from one another.

## Running the tests

Use Cargo:

```shell
$ cargo test
```

## License

See [LICENSE](../../LICENSE) for more details.

Copyright 2020 Auxon Corporation

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

[http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0)

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
