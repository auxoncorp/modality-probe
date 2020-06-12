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

## Concurrency

Since both the debug-collector on the pc-side and the tracers on the microcontroller need to access the same data, there needs to be a mechanism to prevent race conditions that lead to inconsistency.

### Original proposal: CPU halting

The debug-collector reads and writes to the ekotrace logs that the tracers running on the device have access to, so the debug-collector must ensure that it is not accessing logs at the same time as tracers. To do so, we can add an `in_use: AtomicBool` field to the DynamicHistory struct that will be set to true while the tracer is accessing the log. When the debug-collector pulls the logs, it will halt the CPU of the target and then check the value of `in_use`, aborting if true. If `in_use` is false, then the debug-collector can safely access the logs and then unhalt the CPU when finished. The use of atomic CPU instructions by the `AtomicBool` type should prevent race conditions.

Since the debug-collector attempts to pull log data from multiple tracers at once, every iteration, it is possible that some of the tracers are locked. To deal with this, the debug-collector will simply skip the locked tracers. Depending on the logging frequency of tracers, this strategy could occasionally result in waiting multiple iterations to pull a given tracer's logs. Another major downside to this approach is the probe effect that halting the CPU will cause.

### Revised proposal: RaceBuffer

A RaceBuffer is a single-producer, single-consumer, lock free ring buffer. As suggested by the name, the RaceBuffer has data races during operation, but it detects when the data races might have lead to inconsistency. Therefore, it also relies on each read/write to each entry to be atomic. In our case, the entries are ekotrace u32 log entries, and we expect to be running the tracers on 32-bit microcontrollers, so each read/write to a u32 should be atomic.

The main goal behind the buffer is to make it so the reader does not need to write at all. Therefore, the writer does not get any information about actions of the reader. In my prototype implementation, the writer simply writes to a ring buffer, overwriting old data after filling the buffer. The reader periodically performs reads to the buffer, reading all of the new data in the buffer every time a read is performed. It stores the data it reads to an output vector. 

Invariants:
- In the output vector, every entry is at the index that the writer wrote it at. For instance, the 20th entry that the writer wrote would be the 20th element of the output vector. However, since data in the buffer may be overwritten before the reader reads it, any number of the entries in the output vector may be replaced by a nil value which represents that the entries were missed. 
- For two-word entries (like clock entries or entries with a payload), the algorithm guarantees that each two word entry will either be fully included or fully omitted in the ouput vector; there will never be half of a two-word entry included.

#### Writer Algorithm

The writer keeps track of a write cursor, which represents the index of the next write. This cursor is incremented every time a write happens, and is not reset when the end of the backing storage is reached. Therefore, the actual index of the backing storage is calculated as: `write_cursor % len_of_storage`.

The writer performs a write by:
1. Set value at write cursor to nil
2. Increment write cursor
3. Write data at `write_cursor - 1`

These steps make it so that if present, the entry in front of the write cursor is the oldest entry in the buffer, and the entry behind the write cursor is the youngest. If a nil value is present in front of the write cursor, then it represents that the oldest entry has been overwritten. If a nil value is present behind the write cursor, it represents that the youngest value has not yet been written.

#### Reader Algorithm

The reader keeps track of a read cursor, which represents the index of the next entry that will be read, which is always the oldest entry that has not yet been read or missed. Similar to the write cursor, the read cursor is not reset upon reaching the end of the backing storage. The reader also needs a way to read the value of the write cursor and to read values from the backing storage. In our case, that is done over JTAG/SWD. 

The basic idea behind the reader is that it reads the value of the write cursor at the start of the read to figure out what data in the buffer is new. It reads this data from the backing storage, then reads the value of write cursor to see if any of the data may have been overwritten during the read. If it is possible that an entry was overwritten before the reader read it, then that entry is considered to be missed. 

The reader performs a read (of all new data in the buffer) by:
1. Set `pre_wcurs` to write cursor
2. Calculate number of entries missed (not read and overwritten) between writes, append that many nil values to output buffer
3. If the write cursor lapped the read cursor (i.e. if any entries were missed), set the read cursor to the oldest entry available based on `pre_wcurs`.
4. Set `first_read` to read cursor.
5. Read values from backing storage between `first_read` and `pre_wcurs`, in order from oldest to youngest, while incrementing read cursor. Store these values in a temporary read buffer
6. Set `post_wcurs` to write cursor
7. Calculate `overlap`, which is equal to the number of entries after `first read` that may have been overwritten before they were read, based on `post_wcurs`. Ignore these entries and instead append nil entries to the output vector.
8. The rest of the values in the temporary read buffer are guaranteed to be correct and present, except that there may be a nil value at the start or end of the temporary buffer:
    - nil value at start (in front of write cursor): This means the oldest value was overwritten, so reading a nil value instead of the entry is the expected behavior.
    - nil value at end (behind write cursor): This means the youngest value has yet to be written, meaning the reader will ignore the nil value and decrement the read cursor by one, in order to read that entry on the next read.
    - Other than the case of a nil value at the end, the entries in the temporary buffer can be appended to the end of the output vector.

#### Two-word entries

To maintain consistency of two-word entries, the writer simply will check if it is overwriting a two-word entry, will nillify both entries, starting with the second, and then will increment the head by two. This will leave an extra nil value behind the head, which will be filled upon the next write.

When reading, the reader also must check if both of the last two values of its temporary read buffer are nil instead of just the last. If a reader reads a prefix of a two-word entry but then misses the suffix, then the prefix will be replaced by a nil value in the output vector.

#### Next steps

A prototype is fully implemented, and has no known issues. It holds up against random timouts between a large number of reads and writes. More thorough testing of the prototype could be done by adding random timeouts to the internals of the data structure in order to target more extreme edge cases. Beyond that, we will probably need to do model checking to verify that the buffer works in all cases.

#### Changes to ekotrace

This data structure would replace the current structure for holding compact log entries. The RaceBufferReader requires the std library, but adding functionality to read from the writer structure itself would be trivial if concurrency is not necessary or if locking systems are available. Adding this functionality would be necessary so that log reports can be created if a UDP collector is in use.
  

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
