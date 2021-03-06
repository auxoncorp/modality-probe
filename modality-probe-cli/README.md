# modality-probe-cli
Generate Modality Probe event definitions and declarations and
visualize a trace.

## Overview

The Modality Probe CLI can be used to generate manifests containing
metadata for your events and probes, and then can generate code for
their definitions from those manifests. It can also be used to
visualize a collected trace as Graphviz dot code or to inspect it in
the terminal as a log.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.rs)

### Building
Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), clone this repository and use Cargo to build it
locally:

```shell
$ cd modality-probe/modality-probe-cli
$ cargo install --path .
```

This will deposit a file at
`modality-probe/target/release/modality-probe` that can be run
directly.

## Usage

```
Modality probe command line interface

USAGE:
	modality-probe <SUBCOMMAND>

FLAGS:
	-h, --help   	Prints help information
	-V, --version	Prints version information

SUBCOMMANDS:
	header-gen  	Generate Rust/C header files with event/probe id constants
	help        	Prints this message or the help of the given subcommand(s)
	log         	Inspect a trace in the terminal as a log or an ASCII-based graph
	manifest-gen	Generate component, event and probe manifest files from probe macro invocations
	visualize      	Visualize a collected trace as a Graphviz digraph

```

### Visualize
```
Visualize a collected as a Graphviz digraph

USAGE:
    modality-probe visualize [FLAGS] <graph-type> --components <components>... --report <report>

FLAGS:
    -h, --help
            Prints help information
    -i, --interactions-only
            Generate the graph showing only the causal relationships, eliding the events inbetween
    -V, --version
            Prints version information


OPTIONS:
    -c, --components <components>...
            The path to a component directory. To include multiple components, provide this switch
            multiple times
    -r, --report <report>
            The path to the collected trace

ARGS:
    <graph-type>
            The type of graph to output.

            This can be either `cyclic` or `acyclic`. A cyclic graph is one which shows the
            possible paths from either an event or a probe. An acyclic graph shows the causal
            history of either all events or the interactions between probes in the system.
```

Visualize provides a way to convert your collected trace into a
Graphviz dot graph.


```
$ modality-probe visualize acyclic \
    --components my-component \
    --report session_8_log_entries.csv > complete.dot
```
### Manifest Generation

```
modality-probe-manifest-gen 0.3.0
Generate component, event and probe manifest files from probe macro invocations

USAGE:
    modality-probe manifest-gen [FLAGS] [OPTIONS] <source-path>

FLAGS:
    -h, --help
            Prints help information
        --regen-component-id
            Regenerate the component IDs instead of using existing IDs (if present)
    -V, --version
            Prints version information

OPTIONS:
        --component-name <component-name>
            Component name used when generating a component manifest [default: component]
        --event-id-offset <event-id-offset>
            Event ID offset, starts at 1 if not specified
        --file-extension <file-extensions>...
            Limit the source code searching to files with matching extensions
    -l, --lang <lang>
            Language (C or Rust), if not specified then guess based on file extensions
    -o, --output-path <output-path>
            Output path where component files are generated [default: component]
        --probe-id-range <probe-id-range>
            Constrain the generated probe ID to an specific range.
            This can be either `<inclusive_start>..<exclusive_end>` or
            `<inclusive_start>..=<inclusive_end>`.
            The range values are unsigned 32-bit integers and must be non-zero.

ARGS:
    <source-path>
            Source code path to search
```

Manifest generation works by exploring your source code looking for
probe initialization and event recordings. It then generates a CSV
file that contains the event name, its autogenerated id, as well as
other metadata about the event. This CSV file then serves two
purposes: generating headers files that contain event and probe
definitions which you can read about in the following section, and
secondly, when interacting with a trace after it’s been collected,
such as with the `visualize` command, to convert the raw ids back to
human-readable formats.

```
$ modality-probe manifest-gen .
```
### Header Generation

```
modality-probe-header-gen 0.3.0
Generate Rust/C header files with event/probe id constants

USAGE:
    modality-probe header-gen [OPTIONS] <component-path>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

OPTIONS:
        --include-guard-prefix <include-guard-prefix>
            C header include guard prefix. [default: MODALITY_PROBE]
    -l, --lang <lang>
            The language to output the source in, either `c' or `rust' [default: C]
    -o, --output-path <output-path>
            Write output to file (instead of stdout)

ARGS:
    <component-path>    Component path
```

`header-gen` generates the Rust or C files containing the definitions
for your events and probes. As stated in the previous section, events
and probes, at runtime, use an autogenerated id—an unsigned 32-bit
integer. With `header-gen` you get to use their textual name in your
code, and their name to id mappings are handled through code
generation via this command, and `manifest-gen` before it.

```
$ modality-probe header-gen -o include/probes.h my-component
```

**Note:** you’ll need to run `header-gen` _before_ compilation to give
definitions for those otherwise undefined symbols.

### Log

```
Inspect a trace in the terminal as a log or an ASCII-based graph

USAGE:
    modality-probe log [FLAGS] [OPTIONS] --component-path <component-path>... --report <report>

FLAGS:
        --graph
            Print the log as an ASCII-art graph

    -h, --help
            Prints help information

        --no-color
            Don't colorize the output

    -V, --version
            Prints version information

    -v
            Provide (more) verbose output. (-v, -vv, &c.)


OPTIONS:
        --component <component>
            The component to target. If no component is given, the log from all components is interleaved

    -c, --component-path <component-path>...
            The path to a component directory. To include multiple components, provide this switch multiple times

    -f, --format <format>
            Provide a custom format string to be interpreted by each event
            row.

            The format string may use any combination of the following
            identifiers.

            | Specifier | Data               |
            |-----------|--------------------|
            |    %ei    | Event id           |
            |    %en    | Event name         |
            |    %ef    | Event file         |
            |    %el    | Event line         |
            |    %et    | Event tags         |
            |    %ed    | Event description  |
            |    %et    | Event type hint    |
            |    %ep    | Event payload      |
            |    %er    | Raw event payload  |
            |    %ec    | Event coordinate   |
            |    %eo    | Event clock offset |
            |    %pi    | Probe id           |
            |    %pn    | Probe name         |
            |    %pc    | Probe clock        |
            |    %pd    | Probe description  |
            |    %pf    | Probe file         |
            |    %pl    | Probe line         |
            |    %pt    | Probe tags         |
            |    %ci    | Component id       |
            |    %cn    | Component name     |
            |    %rt    | Receive time       |

            NOTE: If an identifier is used in the string and that field is not
            available on the event, it will be replaced by an empty string.
        --from <from>
            Provide an event coordinate as a starting point for the filters that require it

        --probe <probe>
            The probe to target. If no probe is given, the log from all probes is interleaved

        --radius <radius>
            Filter a whole graph down to the radius around a specific event.

            Takes a number used as the “size” of the radius—the number of events on any path in either direction that
            should be included in the output.

            Requires `--from`.
    -r, --report <report>
            The path to the collected trace
```

Inspect a trace in the terminal. Filter it by probe or component,
provide custom format strings, and optionally output the log as an
interaction graph.

```shell

$ modality-probe log -vv --component-path ./example-component --report session_0_log_entries.jsonl
```

## Running the tests

Use Cargo:

```shell
$ cargo test
```

## License

See [LICENSE](../LICENSE) for more details.

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

