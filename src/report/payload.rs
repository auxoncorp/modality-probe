//! Compact log processing to generate report payloads
use super::chunked::ChunkedReportState;
use crate::compact_log::CompactLogItem;
use crate::history::DynamicHistory;
use crate::{EventId, LogicalClock, ProbeId};

use fixed_slice_vec::FixedSliceVec;

use core::iter::Iterator;
use core::iter::Peekable;
use core::mem::size_of;

/// Collection representing payload output
pub trait PayloadOutput {
    /// Push item to payload
    fn push(&mut self, item: CompactLogItem);
    /// Get capacity of space left in collection
    fn free_capacity(&mut self) -> usize;
}

/// Array-backed collection used to store processed clocks and processed report output
pub trait ReportedClocks {
    /// Merge clock into reported clocks
    fn merge_clock(&mut self, external_id: ProbeId, external_clock: u32);
    /// Get underlying slice
    fn as_slice(&self) -> &[LogicalClock];
}

/// Log payload output backed by a FixedSliceVec
pub struct PayloadOutputFSV<'a, 'b>(&'a mut FixedSliceVec<'b, u8>);

impl<'a, 'b> PayloadOutputFSV<'a, 'b> {
    /// Create new PayloadOutputFSV
    pub fn new(output_fsv: &'a mut FixedSliceVec<'b, u8>) -> PayloadOutputFSV<'a, 'b> {
        PayloadOutputFSV(output_fsv)
    }
}

impl PayloadOutput for PayloadOutputFSV<'_, '_> {
    fn push(&mut self, item: CompactLogItem) {
        for b in &item.raw().to_le_bytes() {
            self.0.push(*b);
        }
    }

    fn free_capacity(&mut self) -> usize {
        (self.0.capacity() - self.0.len()) / size_of::<CompactLogItem>()
    }
}

/// List of reported clocks backed by a FixedSliceVec
pub struct ReportedClocksFSV<'a, 'b>(&'a mut FixedSliceVec<'b, LogicalClock>);

impl<'a, 'b> ReportedClocksFSV<'a, 'b> {
    /// Create new ReportedClocksFSV
    pub fn new(clocks_fsv: &'a mut FixedSliceVec<'b, LogicalClock>) -> ReportedClocksFSV<'a, 'b> {
        ReportedClocksFSV(clocks_fsv)
    }
}

/// Array-backed collection used to store processed clocks and processed report output
impl ReportedClocks for ReportedClocksFSV<'_, '_> {
    fn merge_clock(&mut self, external_id: ProbeId, external_clock: u32) {
        let _ = DynamicHistory::merge_clock(self.0, external_id, external_clock);
    }

    fn as_slice(&self) -> &[LogicalClock] {
        self.0.as_slice()
    }
}

/// Push source clock to processed clocks
pub fn init_frontier_clocks<C>(frontier_clocks: &mut C, source_id: ProbeId)
where
    C: ReportedClocks,
{
    frontier_clocks.merge_clock(source_id, 0);
}

/// Peekable iterator over compact log items that counts how many times next() is called
struct CountedLogPeekable<I>
where
    I: Iterator<Item = Option<CompactLogItem>>,
{
    peekable: Peekable<I>,
    num_iterated: usize,
}

impl<I> CountedLogPeekable<I>
where
    I: Iterator<Item = Option<CompactLogItem>>,
{
    fn new(iter: I) -> Self {
        Self {
            peekable: iter.peekable(),
            num_iterated: 0,
        }
    }

    #[allow(clippy::option_option)]
    fn next(&mut self) -> Option<Option<CompactLogItem>> {
        self.num_iterated += 1;
        self.peekable.next()
    }

    fn peek(&mut self) -> Option<&Option<CompactLogItem>> {
        self.peekable.peek()
    }

    fn num_iterated(&self) -> usize {
        self.num_iterated
    }
}

/// Process as much of the given log iterator as possible into a report, outputting the report into output
/// Returns the number of items in the log that were reported
/// and whether or not all new log items were reported
pub fn write_bulk_report_payload<I, C, O>(
    log_iter: I,
    frontier_clocks: &mut C,
    output: &mut O,
) -> (usize, bool)
where
    I: Iterator<Item = Option<CompactLogItem>>,
    C: ReportedClocks,
    O: PayloadOutput,
{
    if !write_all_clocks(frontier_clocks, output) {
        // If not all clocks can be written in given space, return
        return (0, false);
    }
    let mut log_peekable = CountedLogPeekable::new(log_iter);
    if !count_and_report_missed(&mut log_peekable, output) {
        // No space to write items missed event
        return (0, false);
    }
    if let Some(Some(item)) = log_peekable.peek() {
        if item.has_clock_bit_set()
            && item.interpret_as_logical_clock_probe_id()
                != frontier_clocks.as_slice()[0].id.get_raw()
        {
            // First item after missed is a clock but not source probe clock, indicating a partial clock section
            // proceed by merging clocks without including in report
            merge_clock_section(&mut log_peekable, frontier_clocks);
        }
    }
    let finished = write_log_to_payload(&mut log_peekable, frontier_clocks, output);
    (log_peekable.num_iterated(), finished)
}

/// Write payload of a single chunk of chunked report
/// Returns the number of items in the log that were reported
/// and whether or not all new log items were reported
pub(crate) fn write_chunked_report_payload<I, C, O>(
    log_iter: I,
    frontier_clocks: &mut C,
    output: &mut O,
    report_state: &mut ChunkedReportState,
) -> (usize, bool)
where
    I: Iterator<Item = Option<CompactLogItem>>,
    C: ReportedClocks,
    O: PayloadOutput,
{
    if let Some(next_clock_index) = report_state.next_clock {
        report_state.next_clock = write_clocks(frontier_clocks, output, next_clock_index);
        if report_state.next_clock.is_some() {
            // Initial clock writing is not done, continue in next chunk
            return (0, false);
        }
    }
    let mut log_peekable = CountedLogPeekable::new(log_iter);
    if !report_state.started_looping {
        if !count_and_report_missed(&mut log_peekable, output) {
            // No space to write items missed event
            return (0, false);
        }
        if let Some(Some(item)) = log_peekable.peek() {
            if item.has_clock_bit_set()
                && item.interpret_as_logical_clock_probe_id()
                    != frontier_clocks.as_slice()[0].id.get_raw()
            {
                // First item after missed is a clock but not source probe clock, indicating a partial clock section
                // proceed by merging clocks without including in report
                merge_clock_section(&mut log_peekable, frontier_clocks);
            }
        }
        report_state.started_looping = true;
    }
    let finished = write_log_to_payload(&mut log_peekable, frontier_clocks, output);
    (log_peekable.num_iterated(), finished)
}

/// Write as much of log as possible to output while merging any clocks into reported clocks
/// Returns true if the entire log was written
fn write_log_to_payload<I, C, O>(
    log_peekable: &mut CountedLogPeekable<I>,
    frontier_clocks: &mut C,
    output: &mut O,
) -> bool
where
    I: Iterator<Item = Option<CompactLogItem>>,
    C: ReportedClocks,
    O: PayloadOutput,
{
    loop {
        match log_peekable.peek() {
            None => return true,
            // All missed items are processed at beginning of report
            Some(None) => unimplemented!(),
            Some(Some(peeked_item)) => {
                if peeked_item.has_clock_bit_set() {
                    if output.free_capacity() < 2 {
                        // Could not fit event with payload
                        return false;
                    }
                    // RaceBuffer guarantees that if prefix is present, suffix will also be present
                    let id_item = log_peekable.next().unwrap().unwrap();
                    let count_item = log_peekable.next().unwrap().unwrap();
                    frontier_clocks.merge_clock(
                        ProbeId::new(id_item.interpret_as_logical_clock_probe_id()).unwrap(),
                        count_item.raw(),
                    );
                    output.push(id_item);
                    output.push(count_item);
                } else if peeked_item.has_event_with_payload_bit_set() {
                    if output.free_capacity() < 2 {
                        // Could not fit event with payload
                        return false;
                    }
                    // Push event id and payload to output
                    // RaceBuffer guarantees that if prefix is present, suffix will also be present
                    output.push(log_peekable.next().unwrap().unwrap());
                    output.push(log_peekable.next().unwrap().unwrap());
                } else {
                    // Item is a normal event
                    if output.free_capacity() < 1 {
                        // Could not fit event, indicate that iterator is not finished
                        return false;
                    }
                    // Push event to output
                    output.push(log_peekable.next().unwrap().unwrap());
                }
            }
        }
    }
}

/// Push all reported clocks to output, or return false if there is not enough space to do so
fn write_all_clocks<C, O>(frontier_clocks: &mut C, output: &mut O) -> bool
where
    C: ReportedClocks,
    O: PayloadOutput,
{
    if output.free_capacity() < frontier_clocks.as_slice().len() * 2 {
        // Not enough space to dump clocks
        false
    } else {
        let num_written = write_clocks(frontier_clocks, output, 0);
        // Ensure wrote all clocks
        debug_assert!(num_written.is_none());
        true
    }
}

/// Push as many reported clocks as possible to output, returning how many full clocks were pushed, or None if all
/// remaining clocks were pushed
fn write_clocks<C, O>(frontier_clocks: &mut C, output: &mut O, start: usize) -> Option<usize>
where
    C: ReportedClocks,
    O: PayloadOutput,
{
    let rest_of_clocks = &frontier_clocks.as_slice()[start..];
    let num_clocks_fit = usize::min(rest_of_clocks.len(), output.free_capacity() / 2);
    for c in &rest_of_clocks[..num_clocks_fit] {
        let (id_item, count_item) = CompactLogItem::clock(*c);
        output.push(id_item);
        output.push(count_item);
    }
    if start + num_clocks_fit == frontier_clocks.as_slice().len() {
        None
    } else {
        Some(start + num_clocks_fit)
    }
}

/// Iterate through log, merging all clocks until a non-clock entry is found
fn merge_clock_section<I, C>(log_peekable: &mut CountedLogPeekable<I>, frontier_clocks: &mut C)
where
    I: Iterator<Item = Option<CompactLogItem>>,
    C: ReportedClocks,
{
    loop {
        match log_peekable.peek() {
            None => return,
            Some(None) => return,
            Some(Some(item)) => {
                if !item.has_clock_bit_set() {
                    return;
                }
                // When prefix is present, suffix is guaranteed to be present
                let clock_id = log_peekable
                    .next()
                    .unwrap()
                    .unwrap()
                    .interpret_as_logical_clock_probe_id();
                let clock_count = log_peekable.next().unwrap().unwrap().raw();
                frontier_clocks.merge_clock(ProbeId::new(clock_id).unwrap(), clock_count);
            }
        }
    }
}

/// Iterate through missed items and append missed items event to report payload
fn count_and_report_missed<I, O>(log_peekable: &mut CountedLogPeekable<I>, output: &mut O) -> bool
where
    I: Iterator<Item = Option<CompactLogItem>>,
    O: PayloadOutput,
{
    match log_peekable.peek() {
        Some(None) => (),
        // First item not missed
        _ => return true,
    };
    if output.free_capacity() < 2 {
        // Could not fit log items missed event
        return false;
    }
    let num_nils = count_missed(log_peekable);
    push_log_items_missed(output, num_nils as u32);
    true
}

/// Return size of nil block in given iterator
fn count_missed<I>(log_peekable: &mut CountedLogPeekable<I>) -> usize
where
    I: Iterator<Item = Option<CompactLogItem>>,
{
    let mut num_nils = 0;
    loop {
        let peeked = log_peekable.peek();
        match peeked {
            None => return num_nils,
            Some(None) => {
                log_peekable.next();
                num_nils += 1;
            }
            Some(Some(_)) => return num_nils,
        }
    }
}

/// Append a "logs missed" event to given vector
fn push_log_items_missed<O>(output: &mut O, n: u32)
where
    O: PayloadOutput,
{
    let (event_id_item, payload_item) =
        CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, n);
    output.push(event_id_item);
    output.push(payload_item);
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;

    fn log_to_bytes<'a, 'b>(
        log: &'b [CompactLogItem],
        out_slice: &'a mut [MaybeUninit<u8>],
    ) -> usize {
        let mut out_fsv = FixedSliceVec::new(out_slice);
        let mut out = PayloadOutputFSV(&mut out_fsv);
        for item in log {
            out.push(*item)
        }
        drop(out);
        out_fsv.len()
    }

    #[test]
    fn simple_bulk_payload() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        init_frontier_clocks(&mut ReportedClocksFSV(&mut frontier_clocks), probe_id);

        let log = [
            Some(CompactLogItem::event(EventId::new(1).unwrap())),
            Some(CompactLogItem::event(EventId::new(2).unwrap())),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
            ),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
            ),
        ];

        let mut payload = [MaybeUninit::<u8>::uninit(); 128];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let (num_read, finished) = write_bulk_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
        );
        assert_eq!(num_read, 4);
        assert!(finished);
        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .1,
            CompactLogItem::event(EventId::new(1).unwrap()),
            CompactLogItem::event(EventId::new(2).unwrap()),
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 6 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);
        // Recorded clocks correctly
        assert_eq!(
            frontier_clocks.as_slice(),
            &[LogicalClock {
                id: probe_id,
                count: 1
            }],
        )
    }

    #[test]
    fn bulk_payload_count_missed() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        init_frontier_clocks(&mut ReportedClocksFSV(&mut frontier_clocks), probe_id);

        let log = [
            None,
            None,
            None,
            None,
            Some(CompactLogItem::event(EventId::new(1).unwrap())),
            Some(CompactLogItem::event(EventId::new(2).unwrap())),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
            ),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
            ),
        ];

        let mut payload = [MaybeUninit::<u8>::uninit(); 128];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let (num_read, finished) = write_bulk_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
        );
        assert_eq!(num_read, 8);
        assert!(finished);
        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .1,
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).0,
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).1,
            CompactLogItem::event(EventId::new(1).unwrap()),
            CompactLogItem::event(EventId::new(2).unwrap()),
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);
        // Recorded clocks correctly
        assert_eq!(
            frontier_clocks.as_slice(),
            &[LogicalClock {
                id: probe_id,
                count: 1
            }],
        )
    }

    #[test]
    fn bulk_no_space_for_clocks() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [None, None, None, None];

        let mut payload = [MaybeUninit::<u8>::uninit(); 3 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let (num_read, finished) = write_bulk_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
        );
        assert_eq!(num_read, 0);
        assert!(!finished);
        let expected_payload = [];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);
    }

    #[test]
    fn bulk_no_space_for_missed() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [None, None, None, None];

        let mut payload = [MaybeUninit::<u8>::uninit(); 5 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let (num_read, finished) = write_bulk_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
        );
        assert_eq!(num_read, 0);
        assert!(!finished);
        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);
    }

    #[test]
    fn bulk_partial_start_clocks() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 3,
                })
                .0,
            ),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 3,
                })
                .1,
            ),
            Some(CompactLogItem::event(EventId::new(1).unwrap())),
            Some(CompactLogItem::event(EventId::new(2).unwrap())),
        ];

        let mut payload = [MaybeUninit::<u8>::uninit(); 10 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let (num_read, finished) = write_bulk_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
        );
        assert_eq!(num_read, 4);
        assert!(finished);
        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .1,
            CompactLogItem::event(EventId::new(1).unwrap()),
            CompactLogItem::event(EventId::new(2).unwrap()),
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);
    }

    #[test]
    fn chunked_no_space_for_nils() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [None, None, None, None];

        let mut payload = [MaybeUninit::<u8>::uninit(); 5 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let mut chunked_state = ChunkedReportState::default();

        let (num_read, finished) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
            &mut chunked_state,
        );
        assert_eq!(num_read, 0);
        assert!(!finished);

        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);

        let mut payload_2 = [MaybeUninit::<u8>::uninit(); 5 * size_of::<CompactLogItem>()];
        let mut payload_fsv_2 = FixedSliceVec::new(&mut payload_2);
        let (num_read_2, finished_2) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv_2),
            &mut chunked_state,
        );
        assert_eq!(num_read_2, 4);
        assert!(finished_2);

        let expected_payload_2 = [
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).0,
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 4).1,
        ];
        let mut expected_payload_arr_2 =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len_2 = log_to_bytes(&expected_payload_2, &mut expected_payload_arr_2);
        let expected_payload_raw_2: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr_2[..expected_payload_len_2]) };
        // Payload correct
        assert_eq!(payload_fsv_2.as_slice(), expected_payload_raw_2);
    }

    #[test]
    fn chunked_no_space_for_clocks() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [None, None, None, None];

        let mut payload = [MaybeUninit::<u8>::uninit(); 3 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let mut chunked_state = ChunkedReportState::default();

        let (num_read, finished) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
            &mut chunked_state,
        );
        assert_eq!(num_read, 0);
        assert!(!finished);

        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);

        let mut payload_2 = [MaybeUninit::<u8>::uninit(); 3 * size_of::<CompactLogItem>()];
        let mut payload_fsv_2 = FixedSliceVec::new(&mut payload_2);
        let (num_read_2, finished_2) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv_2),
            &mut chunked_state,
        );
        assert_eq!(num_read_2, 0);
        assert!(!finished_2);

        let expected_payload_2 = [
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .1,
        ];
        let mut expected_payload_arr_2 =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len_2 = log_to_bytes(&expected_payload_2, &mut expected_payload_arr_2);
        let expected_payload_raw_2: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr_2[..expected_payload_len_2]) };
        // Payload correct
        assert_eq!(payload_fsv_2.as_slice(), expected_payload_raw_2);
    }

    #[test]
    fn chunked_partial_clock_section() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mut frontier_clocks_arr = [MaybeUninit::<LogicalClock>::uninit(); 2];
        let mut frontier_clocks = FixedSliceVec::new(&mut frontier_clocks_arr);
        frontier_clocks.push(LogicalClock {
            id: probe_id,
            count: 1,
        });
        frontier_clocks.push(LogicalClock {
            id: other_id,
            count: 2,
        });

        let log = [
            None,
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 3,
                })
                .0,
            ),
            Some(
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 3,
                })
                .1,
            ),
            Some(CompactLogItem::event(EventId::new(1).unwrap())),
            Some(CompactLogItem::event(EventId::new(2).unwrap())),
        ];
        let mut payload = [MaybeUninit::<u8>::uninit(); 5 * size_of::<CompactLogItem>()];
        let mut payload_fsv = FixedSliceVec::new(&mut payload);

        let mut chunked_state = ChunkedReportState::default();

        let (num_read, finished) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv),
            &mut chunked_state,
        );
        assert_eq!(num_read, 0);
        assert!(!finished);

        let expected_payload = [
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 2,
            })
            .1,
        ];
        let mut expected_payload_arr =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len = log_to_bytes(&expected_payload, &mut expected_payload_arr);
        let expected_payload_raw: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr[..expected_payload_len]) };
        // Payload correct
        assert_eq!(payload_fsv.as_slice(), expected_payload_raw);

        let mut payload_2 = [MaybeUninit::<u8>::uninit(); 4 * size_of::<CompactLogItem>()];
        let mut payload_fsv_2 = FixedSliceVec::new(&mut payload_2);
        let (num_read_2, finished_2) = write_chunked_report_payload(
            log.iter().copied(),
            &mut ReportedClocksFSV(&mut frontier_clocks),
            &mut PayloadOutputFSV(&mut payload_fsv_2),
            &mut chunked_state,
        );
        assert_eq!(num_read_2, 5);
        assert!(finished_2);

        let expected_payload_2 = [
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 1).0,
            CompactLogItem::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, 1).1,
            CompactLogItem::event(EventId::new(1).unwrap()),
            CompactLogItem::event(EventId::new(2).unwrap()),
        ];
        let mut expected_payload_arr_2 =
            [MaybeUninit::<u8>::uninit(); 24 * size_of::<CompactLogItem>()];
        let expected_payload_len_2 = log_to_bytes(&expected_payload_2, &mut expected_payload_arr_2);
        let expected_payload_raw_2: &[u8] =
            unsafe { core::mem::transmute(&expected_payload_arr_2[..expected_payload_len_2]) };
        // Payload correct
        assert_eq!(payload_fsv_2.as_slice(), expected_payload_raw_2);
    }
}
