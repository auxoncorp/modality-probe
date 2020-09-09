# FencedRingBuffer

## Overview

A FencedRingBuffer is a ring buffer that can be read by an asynchronous reader (called `FencedReader`) with only read
access to the buffer's state. This is achieved by keeping track of two cursors (or "fences") which represent the ends of 
where valid entries are located in the buffer. The asynchronous reader can detect where data races might have lead to
inconsistency by checking the "fences" before and after reading entries from the buffer. It can then remedy the
situation, potentially by reporting some entries as "missed."

**Guarantees:**
- In the `FencedReader`'s output, all entries will be in the correct order. However, some entries may be omitted if the
  reader was not able to read them before they were overwritten. `FencedReader::read()` returns the number of entries missed
  since the last read, so the number and position of each missed entry is known.
- Two-word entries (which are defined by some attribute of the first word), are kept as an atomic pair, so each
  two word entry will either be fully included or fully omitted in the ouput.

## API

Definition: `WholeEntry` represents either a single entry or a double entry pair.

The `FencedRingBuffer` functions like a normal ring buffer with a head and tail, except that the head will continue overwriting entries
even after it reaches the tail. As a result, the tail may point to an entry that is still in the buffer, so upon the next `pop()`,
the buffer would instead return the oldest entry currently present in the buffer.
`FencedRingBuffer` API: 
- `push(entry: Entry) -> Option<WholeEntry>` - Pushes a new entry to the buffer. If an single or double entry was overwritten to make space, that entry is returned.
- `push_double(entry: Entry, entry: Entry) -> (Option<WholeEntry>, Option<WholeEntry>)` - Similar to `push()` except for double entries. Can return two overwritten entries.
- `num_missed() -> u64` - Returns the number of entries missed between the tail and the oldest entry currently present in the buffer, or 0 if the tail is ahead of or even with 
  the oldest entry.
- `peek() -> Option<WholeEntry>` - Reads the entry at the tail, or the oldest entry present in the buffer if tail has already been overwritten, but does not modify the tail position. 
  Returns `None` if the tail is even with the head.
- `pop() -> Option<WholeEntry>` - Same as `peek()`, except the tail is updated to point to the entry after the one that was popped.
Iteration:
- `drain() -> Iterator<WholeEntry` - returns a draining iterator that uses `pop()` to return entries and move the tail.
- `iter() -> Iterator<WholeEntry>` - returns an iterator that iterates through the items currently present in the buffer, starting from the tail.
  If the tail has already been overwritten, starts at the oldest present entry. Does not move the tail during iteration.

`FencedReader` API:
`read(output: &mut Vec<Entry>) -> Result<u64, Snapper::Error>` - Reads all of the entries currently in the buffer, returning
the number of entries that were missed since the last read. Errors if there was an error while using the reader's `Snapper` to read buffer state.

`Snapper` trait - A structure implementing this trait must be passed to construct a `FencedReader`. This structure
is able to read entries in the buffer's storage as well as the buffer's "write sequence number" and "overwrite sequence number".
These reads should not get reordered, and the sequence number reads must be isolated from writes to those fields by the buffer.
Since the write and overwrite sequence numbers are `u64`s, and 64 bit isolated reads are not possible on 32 bit machines without a using a lock, 
the `Snapper` actually has two functions for each sequence number, one to read the high 32 bits, and the other to read the low 32 bits.
For instance, for the write sequence number, they are `snap_write_seqn_high()` and `snap_write_seqn_low()`.

## Internals

### Sequence numbers
The `FencedRingBuffer` uses monotonically increasing "sequence numbers" to track positions in the buffer instead of cursors
that wrap upon reaching the end of the storage. These sequence numbers are indexed into buffer storage when entries are written or read
by taking the remainder of the sequence number when divided by the storage capacity. This system lets the asynchronous reader know if the buffer has already 
overwritten the next entries that it would have read.

#### Write sequence number (High fence)
The write sequence number is the sequence number of the next entry that will be written. Entries with sequence numbers
greater than or equal to the write sequence number have not been pushed yet, and entries with sequence numbers less
than the write sequence number have been written.

#### Overwrite sequence number (Low fence)
The overwrite sequence number is the sequence number of the next entry that will be overwritten. Entries less than the 
overwrite sequence number were previously written and then overwritten. This sequence number generally tracks 
around a buffer length behind the write sequence number and is incremented when the write sequence number gets
exactly a buffer lenght ahead of it.

By using two cursors, the buffer is able to modify entries while guaranteeing that the asynchronous reader does not misinterpret them.
Entries  with sequence numbers greater than or equal to the overwrite sequence number but also less than the write sequence number
are either not written yet, or are considered "missed." Other entries, even if present in storage,
cannot be safely read, because the writer could be in the process of writing over them and updating the write cursor.

### Asynchronous Reader

The asynchronous reader works by reading the overwrite and write sequence numbers, reading entries that seem to be present in
the buffer based on those sequence numbers (with sequence numbers greater than or equal to the overwrite sequence number,
but less than the write sequence number), and then reading the overwrite sequence number again to see how many of the entries
that were just read may have been overwritten before they were read.

### Two-word/Double entries

Two word entries are entries that are pairs of entries that are grouped together. `is_prefix()`, a function in the `Entry`
trait, should return true for entries that are the first word of a double pair.

To maintain consistency of two-word entries, the writer simply will check if it is overwriting a two-word entry, in which case it will increment the overwrite
cursor by 2 in order to overwrite the whole double entry in one atomic step.

The asynchronous reader also must prevent a prefix from being read and then the suffix getting overwritten. To do so,
when it reads a prefix, that prefix is stored until the suffix is also read. If the entry following the prefix is missed,
the prefix is dropped and treated as a missed entry.