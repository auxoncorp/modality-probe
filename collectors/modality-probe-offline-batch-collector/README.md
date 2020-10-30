# modality-probe-offline-batch-collector

Convert binary report blobs into log files.

## Overview

The offline batch collector is a utility for converting batches
of binary report blobs into log files. It serializes the incoming
reports into json lines and writes those lines to a file.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.rs)

### Building
Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), clone this repository and use Cargo to build it
locally:

```
$ git clone git@github.com:auxoncorp/modality-probe
cd collectors/modality-probe-offline-batch-collector
cargo build --release
```

This will deposit a file at
`modality-probe/target/release/modality-probe-offline-batch-collector` that can
be run directly.

## Usage

```
Utility to convert modality-probe binary reports into log files

USAGE:
    modality-probe-offline-batch-collector [OPTIONS]

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

OPTIONS:
    -i, --input-path <input-path>      Read binary probe report data from a file (instead of stdin)
    -o, --output-file <output-file>    The output file location, defaults to the current directory
    -s, --session-id <session-id>      The session id to associate with the collected trace data [default: 0]
```

```
$modality-probe-offline-batch-collector --input-path ./combined_reports.bin

[2020-10-07T13:05:26Z INFO  modality_probe_offline_batch_collector] Reading from ./combined_reports.bin
[2020-10-07T13:05:26Z INFO  modality_probe_offline_batch_collector] Collected 8 reports from 2 probes in session_0_log_entries.jsonl, 0 reports were discarded
[2020-10-07T13:05:26Z INFO  modality_probe_offline_batch_collector] Processed 1480 bytes, 0 bytes were discarded
[2020-10-07T13:05:26Z INFO  modality_probe_offline_batch_collector] 4 reports from ProbeId 810707595, 0 missed reports
[2020-10-07T13:05:26Z INFO  modality_probe_offline_batch_collector] 4 reports from ProbeId 835613898, 0 missed reports
```

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
