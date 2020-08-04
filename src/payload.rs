//! Compact log processing to generate report payloads
use crate::history::DynamicHistory;
use crate::log::LogEntry;
use crate::{EventId, LogicalClock, ProbeId};
use race_buffer::PossiblyMissed;

use fixed_slice_vec::FixedSliceVec;

use core::fmt;
use core::iter::Iterator;
use core::mem::size_of;

/// Collection representing payload output
///
/// Note: This trait is necessary because report payloads are created at the probe as well the
/// debug collector. The probe must be able to use a slice as the destination, whereas the debug
/// collector uses an expandable Vec.
pub trait PayloadOutput {
    /// Push item to payload
    fn push(&mut self, item: LogEntry);
    /// Get number of additional entries that can fit
    fn free_capacity(&mut self) -> usize;
}

/// Error returned when clock cannot be merged because the clocks list overflowed
pub struct ClocksOverflowedError;

impl fmt::Debug for ClocksOverflowedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Clock cannot be merged because the clocks list overflowed"
        )
    }
}

/// Array-backed collection used to store processed clocks and processed report output
///
/// Note: This trait is necessary because frontier clocks are stored at the probe as well the
/// debug collector. The probe must be able to use a FixedSliceVec, whereas the debug
/// collector uses an expandable Vec.
pub trait FrontierClocks {
    /// Merge clock into reported clocks
    fn merge_clock(
        &mut self,
        external_id: ProbeId,
        external_clock: u32,
    ) -> Result<(), ClocksOverflowedError>;
    /// Get underlying slice
    fn as_slice(&self) -> &[LogicalClock];
}

/// Log payload output backed by a byte slice
pub struct PayloadOutputByteSlice<'a>(FixedSliceVec<'a, u8>);

impl<'a> PayloadOutputByteSlice<'a> {
    /// Create new PayloadOutputByteSlice
    pub fn new(output: &'a mut [u8]) -> PayloadOutputByteSlice<'a> {
        PayloadOutputByteSlice(FixedSliceVec::from_bytes(output))
    }
}

impl PayloadOutput for PayloadOutputByteSlice<'_> {
    fn push(&mut self, item: LogEntry) {
        for b in &item.raw().to_le_bytes() {
            self.0.push(*b);
        }
    }

    fn free_capacity(&mut self) -> usize {
        (self.0.capacity() - self.0.len()) / size_of::<LogEntry>()
    }
}

/// List of frontier clocks backed by a FixedSliceVec
pub struct FrontierClocksFSV<'a, 'b>(&'a mut FixedSliceVec<'b, LogicalClock>);

impl<'a, 'b> FrontierClocksFSV<'a, 'b> {
    /// Create new FrontierClocksFSV
    pub fn new(clocks_fsv: &'a mut FixedSliceVec<'b, LogicalClock>) -> FrontierClocksFSV<'a, 'b> {
        FrontierClocksFSV(clocks_fsv)
    }
}

impl FrontierClocks for FrontierClocksFSV<'_, '_> {
    fn merge_clock(
        &mut self,
        external_id: ProbeId,
        external_clock: u32,
    ) -> Result<(), ClocksOverflowedError> {
        let (epoch, ticks) = crate::unpack_clock_word(external_clock);
        if DynamicHistory::merge_clocks(
            &mut self.0,
            LogicalClock {
                id: external_id,
                epoch,
                ticks,
            },
        )
        .is_err()
        {
            Err(ClocksOverflowedError)
        } else {
            Ok(())
        }
    }

    fn as_slice(&self) -> &[LogicalClock] {
        self.0.as_slice()
    }
}

pub type DidClocksOverflow = bool;
pub type NumEntriesRead = usize;
pub type NumEntriesWritten = usize;

/// Process as much of the given log iterator as possible into a report, outputting the report into output.
/// Returns: The number of items written to the report, the number of items read from the log, and whether or not
/// the clocks list overflowed
///
/// Note: Assumes that output has enough space to fit all frontier clocks.
pub fn write_report_payload<I, C, O>(
    mut log_iter: I,
    frontier_clocks: &mut C,
    output: &mut O,
) -> (NumEntriesWritten, NumEntriesRead, DidClocksOverflow)
where
    I: Iterator<Item = PossiblyMissed<LogEntry>>,
    C: FrontierClocks,
    O: PayloadOutput,
{
    write_clocks(frontier_clocks, output);
    let mut num_read = 0;
    let mut num_written = 0;
    let mut clocks_overflowed = false;
    while let Some(read_entry) = log_iter.next() {
        let cur_entry = if let PossiblyMissed::Entry(e) = read_entry {
            e
        } else {
            // Entry was missed, need to count missed and log internal event
            if output.free_capacity() < 2 {
                // Could not fit log items missed event
                return (num_read, num_written, clocks_overflowed);
            }
            let mut num_missed = 1;
            let mut possible_entry_after_missed = None;
            for possible_missed_entry in &mut log_iter {
                if let PossiblyMissed::Entry(non_missed_entry) = possible_missed_entry {
                    possible_entry_after_missed = Some(non_missed_entry);
                    break;
                } else {
                    num_missed += 1
                }
            }
            num_read += num_missed;
            push_log_items_missed_event(output, num_missed as u32);
            num_written += 2;

            if let Some(e) = possible_entry_after_missed {
                e
            } else {
                // No entries after missed entries, can simply return
                // Note: This should only happen in the debug collector, as the RaceBuffer writer
                // will always have some entries to read after missed entries
                return (num_written, num_read, clocks_overflowed);
            }
        };

        if cur_entry.has_clock_bit_set() {
            if output.free_capacity() < 2 {
                // Could not fit clock
                return (num_read, num_written, clocks_overflowed);
            }
            // RaceBuffer guarantees that if prefix is iterated over/read, then suffix will also be available and present
            let clock_suffix = log_iter.next().unwrap().assume_not_missed();
            // Creating probe ID is safe because the entry was written into the log as a legitimate ID
            // Note: If clocks_overflowed is already true, then merge_clock is guaranteed to return an error, meaning
            // clocks_overflowed will stay true
            clocks_overflowed = frontier_clocks
                .merge_clock(
                    ProbeId::new(cur_entry.interpret_as_logical_clock_probe_id()).unwrap(),
                    clock_suffix.raw(),
                )
                .is_err();
            // Push will not panic, as free capacity is known to be at least 2
            output.push(cur_entry);
            output.push(clock_suffix);
            num_written += 2;
            num_read += 2;
        } else if cur_entry.has_event_with_payload_bit_set() {
            if output.free_capacity() < 2 {
                // Could not fit event with payload
                return (num_read, num_written, clocks_overflowed);
            }
            // RaceBuffer guarantees that if prefix is iterated over/read, then suffix will also be available and present
            let payload = log_iter.next().unwrap().assume_not_missed();
            // Push will not panic, as free capacity is known to be at least 2
            output.push(cur_entry);
            output.push(payload);
            num_written += 2;
            num_read += 2;
        } else {
            // Entry is a normal, single word event
            if output.free_capacity() < 1 {
                // Could not fit event, indicate that iterator is not finished
                return (num_read, num_written, clocks_overflowed);
            }
            // Push will not panic, as free capacity is known to be at least 1
            output.push(cur_entry);
            num_written += 1;
            num_read += 1;
        }
    }
    (num_written, num_read, clocks_overflowed)
}

/// Push frontier clocks to output
/// Note: will panic if not enough space to fit all clocks
fn write_clocks<C, O>(frontier_clocks: &mut C, output: &mut O)
where
    C: FrontierClocks,
    O: PayloadOutput,
{
    for c in frontier_clocks.as_slice() {
        let (id_entry, clock_entry) = LogEntry::clock(*c);
        output.push(id_entry);
        output.push(clock_entry);
    }
}

/// Append a "logs missed" event to the output
///
/// Note: assumes free capacity of output is at least 2
fn push_log_items_missed_event<O>(output: &mut O, n: u32)
where
    O: PayloadOutput,
{
    let (event_id_entry, payload_entry) =
        LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, n);
    output.push(event_id_entry);
    output.push(payload_entry);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ProbeEpoch, ProbeTicks};
    use core::mem::MaybeUninit;

    fn log_to_bytes<'a, 'b>(log: &'b [LogEntry], out_slice: &'a mut [u8]) -> usize {
        let mut out = PayloadOutputByteSlice::new(out_slice);
        let mut n = 0;
        for item in log {
            out.push(*item);
            n += 1;
        }
        drop(out);
        n * size_of::<LogEntry>()
    }

    /// Write a simple payload and merge the clock getting reported
    #[test]
    fn simple_payload() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        FrontierClocksFSV(&mut frontier_clocks)
            .merge_clock(probe_id, 0)
            .unwrap();

        let log = [
            PossiblyMissed::Entry(LogEntry::event(EventId::new(1).unwrap())),
            PossiblyMissed::Entry(LogEntry::event(EventId::new(2).unwrap())),
            PossiblyMissed::Entry(
                LogEntry::clock(LogicalClock {
                    id: probe_id,
                    ticks: ProbeTicks(1),
                    epoch: ProbeEpoch(0),
                })
                .0,
            ),
            PossiblyMissed::Entry(
                LogEntry::clock(LogicalClock {
                    id: probe_id,
                    ticks: ProbeTicks(1),
                    epoch: ProbeEpoch(0),
                })
                .1,
            ),
        ];

        let mut payload = [0u8; 128];
        let (num_written, num_read, did_clocks_overflow) = write_report_payload(
            log.iter().copied(),
            &mut FrontierClocksFSV::new(&mut frontier_clocks),
            &mut PayloadOutputByteSlice::new(&mut payload),
        );
        assert_eq!(num_written, 4);
        assert_eq!(num_read, 4);
        assert!(!did_clocks_overflow);
        let expected_payload = [
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(0),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(0),
                epoch: ProbeEpoch(0),
            })
            .1,
            LogEntry::event(EventId::new(1).unwrap()),
            LogEntry::event(EventId::new(2).unwrap()),
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .1,
        ];
        let mut expected_payload_arr = [0u8; 6 * size_of::<LogEntry>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        let num_frontier_clocks = 1;
        assert_eq!(
            &payload[..(num_written + num_frontier_clocks * 2) * size_of::<LogEntry>()],
            expected_payload_raw
        );
        // Recorded clocks correctly
        assert_eq!(
            frontier_clocks.as_slice(),
            &[LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            }],
        )
    }

    /// Count missed entries and include internal event at start of payload
    #[test]
    fn count_missed() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        FrontierClocksFSV(&mut frontier_clocks)
            .merge_clock(probe_id, 0)
            .unwrap();

        let log = [
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
            PossiblyMissed::Entry(LogEntry::event(EventId::new(1).unwrap())),
            PossiblyMissed::Entry(LogEntry::event(EventId::new(2).unwrap())),
            PossiblyMissed::Entry(
                LogEntry::clock(LogicalClock {
                    id: probe_id,
                    ticks: ProbeTicks(1),
                    epoch: ProbeEpoch(0),
                })
                .0,
            ),
            PossiblyMissed::Entry(
                LogEntry::clock(LogicalClock {
                    id: probe_id,
                    ticks: ProbeTicks(1),
                    epoch: ProbeEpoch(0),
                })
                .1,
            ),
        ];

        let mut payload = [0u8; 128];
        let (num_written, num_read, did_clocks_overflow) = write_report_payload(
            log.iter().copied(),
            &mut FrontierClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputByteSlice::new(&mut payload),
        );
        assert_eq!(num_written, 6);
        assert_eq!(num_read, 8);
        assert!(!did_clocks_overflow);
        let expected_payload = [
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(0),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(0),
                epoch: ProbeEpoch(0),
            })
            .1,
            LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).0,
            LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).1,
            LogEntry::event(EventId::new(1).unwrap()),
            LogEntry::event(EventId::new(2).unwrap()),
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .1,
        ];
        let mut expected_payload_arr = [0u8; 24 * size_of::<LogEntry>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        let num_frontier_clocks = 1;
        assert_eq!(
            &payload[..(num_written + num_frontier_clocks * 2) * size_of::<LogEntry>()],
            expected_payload_raw
        );
        // Recorded clocks correctly
        assert_eq!(
            frontier_clocks.as_slice(),
            &[LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            }],
        )
    }

    /// No space for internal event, don't write anything
    #[test]
    fn no_space_for_missed() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            ticks: ProbeTicks(1),
            epoch: ProbeEpoch(0),
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            ticks: ProbeTicks(2),
            epoch: ProbeEpoch(0),
        });

        let log = [
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
            PossiblyMissed::Missed,
        ];

        let mut payload = [0u8; 5 * size_of::<LogEntry>()];
        let (num_written, num_read, did_clocks_overflow) = write_report_payload(
            log.iter().copied(),
            &mut FrontierClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputByteSlice::new(&mut payload),
        );
        assert_eq!(num_written, 0);
        assert_eq!(num_read, 0);
        assert!(!did_clocks_overflow);
        let expected_payload = [
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: probe_id,
                ticks: ProbeTicks(1),
                epoch: ProbeEpoch(0),
            })
            .1,
            LogEntry::clock(LogicalClock {
                id: other_id,
                ticks: ProbeTicks(2),
                epoch: ProbeEpoch(0),
            })
            .0,
            LogEntry::clock(LogicalClock {
                id: other_id,
                ticks: ProbeTicks(2),
                epoch: ProbeEpoch(0),
            })
            .1,
        ];
        let mut expected_payload_arr = [0u8; 24 * size_of::<LogEntry>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        let num_frontier_clocks = 2;
        assert_eq!(
            &payload[..(num_written + num_frontier_clocks * 2) * size_of::<LogEntry>()],
            expected_payload_raw
        );
    }
}
