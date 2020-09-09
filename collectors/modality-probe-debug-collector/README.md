# modality-probe-debug-collector

## Overview
Read modality-probe logs from microcontrollers using JTAG-based interfaces. Allows for collection of logs with minimal modifications to the target program.

## Getting Started
### Dependencies
The collector requires a Rust toolchain. The recommended toolchain
  management system for Rust is [Rustup](https://rustup.sh).

The collector depends on libusb and libftdi. 
On linux these can be installed with your package manager:
```
# Ubuntu
> sudo apt install -y libusb-dev libusb-1.0 libftdi1-dev
```

On Windows you can use [vcpkg](https://github.com/microsoft/vcpkg#quick-start-windows):

```
# dynamic linking 64-bit
> vcpkg install libftdi1:x64-windows libusb:x64-windows
> set VCPKGRS_DYNAMIC=1

# static linking 64-bit
> vcpkg install libftdi1:x64-windows-static-md libusb:x64-windows-static-md
```

### Building
Once Rust is installed (don’t forget to follow directions about
setting up `$PATH`), clone this repository and use Cargo to build and install 
it locally:

```
$ git clone git@github.com:auxoncorp/modality-probe
cd modality-probe/collectors/modality-probe-debug-collector
cargo install
```

### Choosing an attachment method

#### Directly attach over DAPLink, STLink, or JLink

To directly attach to the target device without external tools, simply use the `--attach <chip-type>` option. 
For instance, to connect to the [NUCLEO-F767ZI board](https://www.st.com/en/evaluation-tools/nucleo-f767zi.html) 
with an STM32 MCU, include the option `--attach stm32`. This method uses the 
[probe-rs](https://github.com/probe-rs/probe-rs) library to attach to the chip, and requires that there is a only 
one single-core cpu linked to the host (collector-side) device.

#### Connect to a GDB server

This option is under development.

### Probe Symbols/Addresses

In order to read logs from the Modality probes on the target device, the collector must locate each probe in memory.
This is acheived by supplying either the address or symbol name of each probe as positional command line arguments.

If the numerical address of a probe struct is known, then it should be in hex format and prefixed with `0x` or `0X`: `0x20000000`.
To automatically resolve the address of a probe, supply the program binary using the `--elf` argument, and then simply
input the symbol name as a positional argument: `PROBE_1`. 

The collector requires that the memory layout of the ELF is the same as that of the program after it is loaded onto the target device.
Therefore, the ELF must be statically linked, and there must not be address space layout randomization (ASLR) at load time.
When flashing microcontrollers, there is no ASLR, and ASLR can be turned off on Linux by using 
`setarch $(uname -m) --addr-no-randomize [<program> [<argument>...]]` to run the program.

To use the symbol/address of a pointer to the probe structure instead of the symbol/address of the structure itself, simply add an
asterisk before the argument: `*0x20000000`, `*PROBE_1`. If `try_initialize_at` or `initialize_at` are used, the probe 
will be embedded at the start of the given storage array, so the address/symbol of the array can be directly used. 
In Rust, supplied symbols must have the `#[no_mangle]` attribute in order to use their
symbol names. C variable symbols are not mangled by default, so no extra step is required.
Using symbols in C++ binaries are not currently supported.

The recommended method to deal with symbol resolution is to either create a global array that the probe will be initialized
in, or to create a global pointer that points to the probe.

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

Since the probe is initialized into `PROBE_STORAGE`, that symbol can be directly supplied to the command line.
Alternatively, the `PROBE_PTR` symbol can be used if it is prefixed with an asterisk: `*PROBE_PTR`.

# Usage

Required options:
- `--attach <chip-type` `-a`: Chip type of target device for direct attachment
OR
- `--gdb-server <gdb-addr>` `-g`: Address of gdb server attached to chip - not currently supported

- `--interval <interval-duration>` `-i`: Interval between collection rounds - at each interval, a report will be generated from each probe. Ex: "2min 15sec 500milli 250micro"
- `--output <output-path>` `-o` : Output file path

Other options/flags:
- `--session-id <session-id>` `-s`: A session id to distinguish the trace data collected during this tracing run. Defaults to 0.
- `--64-bit`; `--32-bit`: Processor word size of the target system. If not given, detected from given ELF if possible. Defaults to 32 bit with warning.
- `--elf <elf-path>` `-e`: ELF to use for symbol resolution and/or architecture detection
- `--reset <init-timeout>` `-r`: Reset the execution of the target device upon starting the collector, then wait 
  `init-timeout` before attempting to read from probe state. If the initialization timeout is not long enough,
  the collector may error when attempting to read uninitialized probe state.

Example:

`modality-probe-debug-collector --session-id 0 --elf ./target-elf --attach stm32 --interval 500milli --output ./out --reset 50milli *0x20001000 PROBE_2 0x20000000 *PROBE_4_PTR PROBE_5`
