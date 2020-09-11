# modality-probe-debug-collector

## Overview
Read modality-probe logs from microcontrollers using JTAG-based
interfaces. Allows for collection of logs with minimal modifications
to the target program.

## Getting Started

### Dependencies

* [Rust Toolchain](https://rustup.sh)
* [libusb](https://libusb.info/)
* [libftd](https://www.intra2net.com/en/developer/libftdi/)

### Building

Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), clone this repository and use Cargo to build and
install it locally:

```
$ git clone git@github.com:auxoncorp/modality-probe
$ cd modality-probe/collectors/modality-probe-debug-collector
$ cargo install --path .
```

## Usage

```
modality-probe-debug-collector 0.1.0
Periodically collects logs from microcontrollers over debug interfaces; outputs them to a file.

USAGE:
    modality-probe-debug-collector [FLAGS] [OPTIONS] --attach <chip-type> --gdb-addr <gdb-addr> --interval <interval-duration> --output <output-path> [probe-syms]...

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information
        --32-bit     Specifies 32 bit architecture of target system
        --64-bit     Specifies 64 bit architecture of target system

OPTIONS:
    -a, --attach <chip-type>              Chip type of target device for direct attachment
    -e, --elf <elf-path>                  Path of ELF file for symbol resolution and/or architecture detection
    -g, --gdb-addr <gdb-addr>             Address of gdb server attached to chip
    -r, --reset <init-timeout>            Reset the execution of the target device upon starting the collector, then
                                          wait `init-timeout` before attempting to read from probe state. If the
                                          initialization timeout is not long enough, the collector may error when
                                          attempting to read uninitialized probe state
    -i, --interval <interval-duration>    Interval between collection rounds Ex: "2 min 15 sec 500 milli 250 micro"
    -o, --output <output-path>            Output file path
    -s, --session-id <session-id>         Session id to associate with the collected trace data [default: 0]

ARGS:
    <probe-syms>...    Symbols and/or raw addresses of probes or probe pointers. Raw addresses should be in hex
                       format, prefixed with '0x' or '0X' Probe pointer addresses and symbols should be prefixed
                       with `*`. Ex: *0X100 0x104 symbol1 *symbol2 0X108 *0x10c
```

```shell
$ modality-probe-debug-collector --session-id 0 \
    --elf ./target-elf \
    --attach stm32 \
    --interval 500milli \
    --output ./out \
    --reset 50milli \
    *0x20001000 PROBE_2 0x20000000 *PROBE_4_PTR PROBE_5
```

## Running the Tests

To run tests you'll need the `thumbv7em-none-eabihf` target
installed. Use Rustup to add it, then you can use Cargo to run the
tests.

``` shell
$ rustup target add thumbv7em-none-eabihf
$ cargo test
```

## Choosing an attachment method

### Directly attach over DAPLink, STLink, or JLink

To directly attach to the target device without external tools, simply
use the `--attach <chip-type>` option. For instance, to connect to
the [NUCLEO-F767ZI
board](https://www.st.com/en/evaluation-tools/nucleo-f767zi.html) with
an STM32 MCU, include the option `--attach stm32`. This method uses
the [probe-rs](https://github.com/probe-rs/probe-rs) library to attach
to the chip, and requires that there is a only one single-core cpu
linked to the host (collector-side) device.

### Connect to a GDB server

This option is under development.

## Probe Symbols/Addresses

In order to read logs from the Modality probes on the target device,
the collector must locate each probe in memory. This is acheived by
supplying either the address or symbol name of each probe as
positional command line arguments.

If the numerical address of a probe struct is known, then it should be
in hex format and prefixed with `0x` or `0X`: `0x20000000`. To
automatically resolve the address of a probe, supply the program
binary using the `--elf` argument, and then simply input the symbol
name as a positional argument: `PROBE_1`.

The collector requires that the memory layout of the ELF is the same
as that of the program after it is loaded onto the target device.
Therefore, the ELF must be statically linked, and there must not be
address space layout randomization (ASLR) at load time. When flashing
microcontrollers, there is no ASLR, and ASLR can be turned off on
Linux using

```shell
$ setarch $(uname -m) --addr-no-randomize [<program> [<argument>...]]
```

To use the symbol/address of a pointer to the probe structure instead
of the symbol/address of the structure itself, simply add an asterisk
before the argument: `*0x20000000`, `*PROBE_1`. If `try_initialize_at`
or `initialize_at` are used, the probe will be embedded at the start
of the given storage array, so the address/symbol of the array can be
directly used. In Rust, supplied symbols must have the `#[no_mangle]`
attribute in order to use their symbol names. C variable symbols are
not mangled by default, so no extra step is required. Using symbols
in C++ binaries are not currently supported.

The recommended method to deal with symbol resolution is to either
create a global array that the probe will be initialized in, or to
create a global pointer that points to the probe.

Example:

```rust
#[no_mangle]
static mut PROBE_STORAGE: [u8; 1024] = [0u8; 1024];
#[no_mangle]
static mut PROBE_PTR: *const ModalityProbe = 0 as *const ModalityProbe;

fn main() {
    let probe: &mut ModalityProbe = unsafe {
        ModalityProbe::try_initialize_at(
            &mut PROBE_STORAGE,
            1,
            RestartCounterProvider::NoRestartTracking
        )
    }.expect("Could not initialize probe");
    unsafe { PROBE_PTR = probe as *const ModalityProbe };
    ...
```

Since the probe is initialized into `PROBE_STORAGE`, that symbol can
be directly supplied to the command line. Alternatively, the
`PROBE_PTR` symbol can be used if it is prefixed with an asterisk:
`*PROBE_PTR`.

## License

See [LICENSE](../../LICENSE) for more details.

```
Copyright 2020 Auxon Corporation

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```
