# Summary

The ekotrace-debug-collector collects and outputs tracer log reports over debug interfaces on a user-defined interval. The user inputs memory locations of tracers or tracer symbols along with the corresponding elf file, and the debug-collector logs reports from those tracers to an output file. The debug collector also allows the user to choose the method of connecting to the target device, either using probe-rs to directly attach, or by connecting to an attached gdb server.

# Motivation

The user may wish to collect ekotrace logs from a microcontroller with no networking capabilities. This tool allows for collection using JTAG/SWD wire protocols instead of UDP.

# Technical Strategy

## Memory Access

To access memory correctly, the program needs to know the word size and endianness of the target. The user can either pass an ELF file containing this information into the CLI: `--elf`, or they can specify the information explicitly: `--word-size 32 --big-endian`.

### Choice of backend

The collector will access memory on the target device either by using the probe-rs Rust library, or by talking to a gdb server that is attached to the target. This choice will be given to the user of the CLI, using `--attach` for probe-rs, or `--gdb-host` to use gdb.

#### probe-rs

probe-rs provides functions to attach to chips over a usb connection, as well as to read from or write to memory locations.

To use this option, users must specify the type of chip that they wish to connect to, which is required by probe-rs: `--attach stm32`.

#### gdb

If the user already has a GDB server that attaches to the chip set up (e.g. OpenOCD), or would rather use such a tool to attach to the target, then they can specify the address of the gdb server that they are running: `--gbd-host localhost:3333`.

In this case, the debug-collector will communicate to the given gdb server over TCP in order to read and write to memory.

### repr(C)

Rust's ABI is undefined, so the representation of structures in memory is unpredictable across compiler versions and architectures. To allow the debug-collector to understand the raw binary it reads from the chip, the ekotrace log data structures must have the `repr(C)` attribute, which tells the compiler to use C's representation of structs in binary. To find the fields of `repr(C)` structs, the debug-collector uses constant offsets for each given word size. This method is fragile to implementation changes to the structs that the debug-collector is accessing.

We would have to add this attribute to `DynamicHistory` and `ChunkedReportState` in ekotrace as well as to `FixedSliceVec` in fixed-slice-vec.

## Symbol resolution

For each tracer, the user will either pass in the memory location of a pointer to the tracer, or will pass in the name of the symbol of the pointer to the tracer. If the latter is used, then the user would also need to pass in an ELF file containing the symbol table of the program running on the target device. The debug-collector will automatically find the memory location of the given symbol by looping through the given symbol table.

## Locking

The debug-collector reads and writes to the ekotrace logs that the tracers running on the device have access to, so the debug-collector must ensure that it is not accessing logs at the same time as tracers. To do so, we can add an `in_use: Atomic<bool>` field to the DynamicHistory struct that will be set to true while the tracer is accessing the log. When the debug-collector pulls the logs, it will halt the CPU of the target and then check the value of `in_use`, aborting if true. If `in_use` is false, then the debug-collector can safely access the logs and then unhalt the CPU when finished. The use of atomic CPU instructions by the `Atomic<bool>` type should prevent race conditions.

Since the debug-collector attempts to pull log data from multiple tracers at once, every iteration, it is possible that some of the tracers are locked. To deal with this, the debug-collector will simply skip the locked tracers. Depending on the logging frequency of tracers, this strategy could occasionally result in waiting multiple iterations to pull a given tracer's logs.

# CLI design
Tracer memory locations or symbols are inputted as positional arguments. If the argument starts with 0x, the CLI interprets the rest of the argument as a hex address of a tracer reference. Otherwise, the CLI interprets the argument as a symbol of a tracer reference, in which case the program binary must be included.

Example:

`ekotrace-debug-collector-cli --session-id 0 --word-size 32 --little-endian --elf ./target-elf --attach stm32 --interval 500 --output-file ./out.csv 0x20001000 TRACER_1 0x20000000 TRACER_3 TRACER_4`

Flags:
- `--session-id` `-s`: a session id to distinguish the trace data collected during this tracing run
- `--word-size` `-w`: processor word size of the target system. If not given, detected from elf file if possible. Defaults to 32 with warning.
- `--little-endian` `-le`; `--big-endian` `-be`: endianness of target system. If not given, detected from elf file if possible. Defaults to little with warning.
- `--elf` `-e`: ELF file to use for symbol resolution and/or architecture detection
- `--attach` `-a`: chip type passed to probe-rs
- `--gdb-server` `-g`: address of gdb server attached to chip
- `--interval` `-i`: interval between log report attempts
- `--output-file` `-o`: a path to the CSV file where the data will be logged


# Open Questions

- Is probe-rs compatible with a wide enough variety of devices? (unclear to me whether it works with word sizes other than 32-bit)
- Other than elf files, what situations regarding target binaries will we need to handle?
