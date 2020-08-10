use core::{
    cmp,
    convert::TryFrom,
    mem::{align_of, size_of},
};

use fixed_slice_vec::{
    single::{EmbedValueError, SplitUninitError},
    FixedSliceVec, TryPushError,
};
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

use race_buffer::buffer::WholeEntry;
use crate::{
    log::{LogEntry, RaceLog},
    wire::{report::WireReport, WireCausalSnapshot},
    CausalSnapshot, EventId, LogicalClock, MergeError, ModalityProbeInstant, OrdClock, ProbeEpoch,
    ProbeId, ProbeTicks, ProduceError, ReportError, StorageSetupError,
};

pub const MIN_CLOCKS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_CLOCKS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + 3 * size_of::<u32>()
    + MIN_CLOCKS_LEN * size_of::<LogicalClock>()
    + MIN_LOG_LEN * size_of::<LogEntry>();

#[cfg(target_pointer_width = "32")]
const_assert_eq!(align_of::<u64>(), align_of::<DynamicHistory>());
#[cfg(not(target_pointer_width = "32"))]
const_assert_eq!(align_of::<usize>(), align_of::<DynamicHistory>());

const_assert_eq!(4, align_of::<LogicalClock>());
const_assert_eq!(4, align_of::<LogEntry>());

assert_eq_size!(u64, LogicalClock);
assert_eq_align!(u32, LogicalClock);

assert_eq_size!(u32, LogEntry);
assert_eq_align!(u32, LogEntry);

const_assert_eq!(12, size_of::<CausalSnapshot>());
const_assert_eq!(4, align_of::<CausalSnapshot>());

const_assert_eq!(12, size_of::<ModalityProbeInstant>());
const_assert_eq!(4, align_of::<ModalityProbeInstant>());

const_assert_eq!(
    size_of::<ProbeId>()
        + size_of::<u32>()
        + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<LogicalClock>()
        + size_of::<RaceLog<'_>>()
        + size_of::<u64>(),
    size_of::<DynamicHistory>()
);

/// Manages the core of a probe in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and probe log items
#[derive(Debug)]
#[repr(C)]
pub struct DynamicHistory<'a> {
    pub(crate) probe_id: ProbeId,
    /// The number of events seen since the current
    /// probe's logical clock last increased.
    pub(crate) event_count: u32,
    /// Invariants:
    ///   * The first clock is always that of the local probe id
    pub(crate) clocks: FixedSliceVec<'a, LogicalClock>,
    pub(crate) self_clock: LogicalClock,
    pub(crate) log: RaceLog<'a>,
    pub(crate) report_seq_num: u64,
}

#[derive(Debug)]
struct ClocksFullError;

impl<'a> DynamicHistory<'a> {
    #[inline]
    pub fn new_at(
        destination: &mut [u8],
        probe_id: ProbeId,
    ) -> Result<&mut DynamicHistory, StorageSetupError> {
        let remaining_bytes = destination.len();
        if remaining_bytes < MIN_HISTORY_SIZE_BYTES {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        if destination.as_ptr().is_null() {
            return Err(StorageSetupError::NullDestination);
        }
        let history = match fixed_slice_vec::single::embed(destination, |dynamic_region_slice| {
            DynamicHistory::new(dynamic_region_slice, probe_id)
        }) {
            Ok(v) => Ok(v),
            Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::Unalignable)) => {
                Err(StorageSetupError::UnderMinimumAllowedSize)
            }
            Err(EmbedValueError::SplitUninitError(SplitUninitError::ZeroSizedTypesUnsupported)) => {
                const_assert!(size_of::<DynamicHistory>() > 0);
                panic!("Static assertions ensure that this structure is not zero sized")
            }
            Err(EmbedValueError::ConstructionError(e)) => Err(e),
        }?;
        {
            let history_ptr = history as *mut DynamicHistory as usize;
            let clocks_ptr = history.clocks.as_slice().as_ptr() as usize;
            assert!(
                 history_ptr + size_of::<DynamicHistory>() <= clocks_ptr,
                "clocks pointer {:#X} should not overlap header [{:#X}..{:#X}] bytes, but they overlapped by {} bytes",
                clocks_ptr, history_ptr, history_ptr + size_of::<DynamicHistory>(), history_ptr + size_of::<DynamicHistory>() - clocks_ptr
            );
            assert!(
                clocks_ptr as usize + history.clocks.capacity() * size_of::<LogicalClock>()
                    <= history.log.as_slice().as_ptr() as usize,
                "log pointer should not overlap clock bytes"
            );
        }

        Ok(history)
    }

    #[inline]
    fn new(
        dynamic_region_slice: &'a mut [u8],
        probe_id: ProbeId,
    ) -> Result<Self, StorageSetupError> {
        let max_n_clocks = cmp::max(
            MIN_CLOCKS_LEN,
            dynamic_region_slice.len() / 8 / size_of::<LogicalClock>(),
        );
        let clocks_region_bytes = max_n_clocks * size_of::<LogicalClock>();
        if clocks_region_bytes > dynamic_region_slice.len() {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        let (clocks_region, log_region) = dynamic_region_slice.split_at_mut(clocks_region_bytes);
        let mut clocks = FixedSliceVec::from_bytes(clocks_region);
        let log = RaceLog::from_bytes(log_region);
        if clocks.capacity() < MIN_CLOCKS_LEN || (log.capacity() as usize) < MIN_LOG_LEN {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        clocks
            .try_push(LogicalClock {
                id: probe_id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            })
            .expect(
                "The History.clocks field should always contain a clock for this probe instance",
            );
        let history = DynamicHistory {
            report_seq_num: 0,
            event_count: 0,
            self_clock: LogicalClock {
                id: probe_id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
            probe_id,
            clocks,
            log,
        };
        Ok(history)
    }

    #[inline]
    fn merge_overwritten_clock(&mut self, overwritten: Option<WholeEntry<LogEntry>>) {
        match overwritten {
            OverwrittenEntry::Double(one, two) => {
                // If what we get out of the log is a clock, merge it into clocks list
                if one.has_clock_bit_set() {
                    if let Some(id) = ProbeId::new(one.interpret_as_logical_clock_probe_id()) {
                        let (epoch, ticks) = crate::unpack_clock_word(two.raw());
                        self.merge_clock(LogicalClock { id, epoch, ticks });
                    }
                }
                self.log_items_missed = self.log_items_missed.saturating_add(2)
            }
            OverwrittenEntry::Single(_) => {
                self.log_items_missed = self.log_items_missed.saturating_add(1)
            }
            OverwrittenEntry::None => (),
        }
    }

    /// Add an item to the internal log that records this event
    /// occurred.
    ///
    /// Note: this function overwrites older events in the log if it
    /// is full.
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        // N.B. point for future improvement - basic compression here
        let overwritten = self.log.push_event(event_id);
        self.merge_overwritten_clock(overwritten);
        self.event_count = self.event_count.saturating_add(1);
    }

    /// Add the event and its payload to the internal log, recording
    /// that this event occurred.
    ///
    /// Note: this function overwrites older events in the log if it
    /// is full.
    #[inline]
    pub(crate) fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        let (first_overwritten, second_overwritten) =
            self.log.push_event_with_payload(event_id, payload);
        self.merge_overwritten_clock(first_overwritten);
        self.merge_overwritten_clock(second_overwritten);
        self.event_count = self.event_count.saturating_add(1);
    }

    /// Increments the clock in the logical clock corresponding to this probe instance
    #[inline]
    fn increment_local_clock(&mut self) {
        // N.B. We rely on the fact that the first member of the clocks
        // collection is always the clock for this probe
        self.self_clock.increment();
        self.event_count = 0;
    }

    #[inline]
    pub(crate) fn now(&self) -> ModalityProbeInstant {
        ModalityProbeInstant {
            clock: self.self_clock,
            event_count: self.event_count,
        }
    }

    pub(crate) fn report(&mut self, destination: &mut [u8]) -> Result<usize, ReportError> {
        // If we can't store at least a header and one event, it's a hard error
        if destination.len() < WireReport::<&[u8]>::buffer_len(0, 1) {
            return Err(ReportError::InsufficientDestinationSize);
        }

        let self_clock = self.self_clock;
        let mut report = WireReport::new_unchecked(destination);
        report.set_fingerprint();
        report.set_probe_id(self.probe_id);
        report.set_clock(crate::pack_clock_word(self_clock.epoch, self_clock.ticks));

        // We can't store at least the frontier clocks and a single two-word item
        if report.as_ref().len() < WireReport::<&[u8]>::buffer_len(self.clocks.len(), 2) {
            report.set_seq_num(self.report_seq_num);
            report.set_n_clocks(0);
            report.set_n_log_entries(1);
            let payload = report.payload_mut();
            payload[..size_of::<LogEntry>()].copy_from_slice(
                &EventId::EVENT_INSUFFICIENT_REPORT_BUFFER_SIZE
                    .get_raw()
                    .to_le_bytes(),
            );
        } else {
            let clocks_len = self.clocks.len();
            report.set_seq_num(self.report_seq_num);
            report.set_n_clocks(clocks_len as u16);

            let payload = report.payload_mut();
            for (c, dest_bytes) in self
                .clocks
                .iter()
                .zip(payload.chunks_exact_mut(size_of::<LogicalClock>()))
            {
                let (first, second) = LogEntry::clock(*c);
                dest_bytes[0..4].copy_from_slice(&first.raw().to_le_bytes());
                dest_bytes[4..8].copy_from_slice(&second.raw().to_le_bytes());
            }

            // If we need to report missed items, account for the event with payload
            let n_log_entries_ready_to_report = if self.log_items_missed != 0 {
                2 + self.log.len()
            } else {
                self.log.len()
            };

            let clock_bytes = clocks_len * size_of::<LogicalClock>();
            let n_log_entries_possible = cmp::min(
                (payload.len() - clock_bytes) / size_of::<LogEntry>(),
                n_log_entries_ready_to_report,
            );

            let mut did_clocks_overflow = false;
            let mut n_copied = 0;
            let mut clock_id = None;
            let mut found_multi_item = false;
            let clocks = &mut self.clocks;
            let mut byte_cursor = clock_bytes;

            if self.log_items_missed != 0 {
                let (first, second) = LogEntry::event_with_payload(
                    EventId::EVENT_LOG_ITEMS_MISSED,
                    self.log_items_missed,
                );
                let dest_bytes = &mut payload[byte_cursor..byte_cursor + 2 * size_of::<LogEntry>()];
                dest_bytes[0..4].copy_from_slice(&first.raw().to_le_bytes());
                dest_bytes[4..8].copy_from_slice(&second.raw().to_le_bytes());
                byte_cursor += 2 * size_of::<LogEntry>();
                n_copied += 2;
            }

            // We peek the next entry so that we never throw away the first item
            // in a double-item log entry if we decide to bail out early due
            // hitting the destination buffer capacity
            while let Some(peeked_entry) = self.log.peek_entry() {
                if n_copied >= n_log_entries_possible {
                    break;
                }

                let dest_bytes = &mut payload[byte_cursor..byte_cursor + size_of::<LogEntry>()];

                if !found_multi_item && peeked_entry.has_clock_bit_set() {
                    // Make sure there's room for the second-item epoch/ticks
                    if n_copied <= n_log_entries_possible - 2 {
                        dest_bytes.copy_from_slice(&peeked_entry.raw().to_le_bytes());
                        clock_id = ProbeId::new(peeked_entry.interpret_as_logical_clock_probe_id());
                        n_copied += 1;
                        found_multi_item = true;
                    } else {
                        // Not enough space for the second item in the double-item entry,
                        // break out of the loop here, and don't consume
                        // the first peeked item
                        break;
                    }
                } else if !found_multi_item && peeked_entry.has_event_with_payload_bit_set() {
                    // Make sure there's room for the second-item payload
                    if n_copied <= n_log_entries_possible - 2 {
                        dest_bytes.copy_from_slice(&peeked_entry.raw().to_le_bytes());
                        n_copied += 1;
                        found_multi_item = true;
                    } else {
                        // Not enough space for the second item in the double-item entry,
                        // break out of the loop here, and don't consume
                        // the first peeked item
                        break;
                    }
                } else {
                    dest_bytes.copy_from_slice(&peeked_entry.raw().to_le_bytes());
                    if let Some(id) = clock_id {
                        let (epoch, ticks) = crate::unpack_clock_word(peeked_entry.raw());
                        if Self::merge_clocks(clocks, LogicalClock { id, epoch, ticks }).is_err() {
                            did_clocks_overflow = true;
                        }
                        clock_id = None;
                    }
                    found_multi_item = false;
                    n_copied += 1;
                }

                // We know we have at least enough space for the
                // next item (if it's a double item entry) at this point, so
                // it's now safe to pop the currently peek'd entry from our log.
                let consumed_entry = self.log.pop_entry();
                debug_assert_eq!(consumed_entry, Some(peeked_entry));

                byte_cursor += size_of::<LogEntry>();
            }

            report.set_n_log_entries(n_copied as u32);

            if did_clocks_overflow {
                self.record_event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED);
            }
        }

        self.report_seq_num = self.report_seq_num.wrapping_add(1);
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);
        self.log_items_missed = 0;

        Ok(WireReport::<&[u8]>::header_len() + report.payload_len())
    }

    #[inline]
    pub(crate) fn produce_snapshot(&mut self) -> Result<CausalSnapshot, ProduceError> {
        let snap = CausalSnapshot {
            clock: self.self_clock,
            reserved_0: 0,
            reserved_1: 0,
        };
        self.increment_local_clock();
        self.write_clocks_to_log(&[self.self_clock]);
        Ok(snap)
    }

    #[inline]
    pub(crate) fn produce_snapshot_bytes(
        &mut self,
        destination: &mut [u8],
    ) -> Result<usize, ProduceError> {
        let mut s = WireCausalSnapshot::new_unchecked(destination);
        s.check_len()?;
        s.set_probe_id(self.self_clock.id);
        s.set_epoch(self.self_clock.epoch);
        s.set_ticks(self.self_clock.ticks);
        s.set_reserved_0(0);
        s.set_reserved_1(0);
        self.increment_local_clock();
        self.write_clocks_to_log(&[self.self_clock]);
        Ok(WireCausalSnapshot::<&[u8]>::min_buffer_len())
    }

    #[inline]
    pub(crate) fn merge_snapshot(
        &mut self,
        external_history: &CausalSnapshot,
    ) -> Result<(), MergeError> {
        self.merge_internal(
            external_history.clock.id,
            external_history.clock.epoch,
            external_history.clock.ticks,
        )
    }

    #[inline]
    pub(crate) fn merge_snapshot_bytes(&mut self, source: &[u8]) -> Result<(), MergeError> {
        let external_history = CausalSnapshot::try_from(source)?;
        self.merge_internal(
            external_history.clock.id,
            external_history.clock.epoch,
            external_history.clock.ticks,
        )
    }

    #[inline]
    fn merge_internal(
        &mut self,
        external_id: ProbeId,
        external_epoch: ProbeEpoch,
        external_clock: ProbeTicks,
    ) -> Result<(), MergeError> {
        self.increment_local_clock();
        self.write_clocks_to_log(&[
            self.self_clock,
            LogicalClock {
                id: external_id,
                epoch: external_epoch,
                ticks: external_clock,
            },
        ]);
        Ok(())
    }

    #[inline]
    fn write_clocks_to_log(&mut self, clocks: &[LogicalClock]) {
        for c in clocks.iter() {
            let (first_overwritten, second_overwritten) = self.log.push_clock(*c);
            self.merge_overwritten_clock(first_overwritten);
            self.merge_overwritten_clock(second_overwritten);
        }
    }

    #[inline]
    fn merge_clock(&mut self, ext_clock: LogicalClock) {
        if Self::merge_clocks(&mut self.clocks, ext_clock).is_err() {
            self.record_event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED);
        }
    }

    #[inline]
    pub(crate) fn merge_clocks<'c>(
        clocks: &mut FixedSliceVec<'c, LogicalClock>,
        ext_clock: LogicalClock,
    ) -> Result<(), TryPushError<LogicalClock>> {
        let mut existed = false;
        for c in clocks.iter_mut() {
            if c.id == ext_clock.id {
                if OrdClock(ext_clock.epoch, ext_clock.ticks) > OrdClock(c.epoch, c.ticks) {
                    c.epoch = ext_clock.epoch;
                    c.ticks = ext_clock.ticks;
                }
                existed = true;
            }
        }
        if !existed {
            clocks.try_push(ext_clock)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn epoch_rollover() {
        let probe_a = ProbeId::new(1).unwrap();
        let probe_b = ProbeId::new(2).unwrap();

        let lc = |id: ProbeId, epoch: u16, clock: u16| LogicalClock {
            id,
            epoch: ProbeEpoch(epoch),
            ticks: ProbeTicks(clock),
        };

        let find_clock =
            |h: &DynamicHistory, id: ProbeId| h.clocks.iter().find(|c| c.id == id).cloned();

        {
            let mut storage_a = [0u8; 512];
            let h = DynamicHistory::new_at(&mut storage_a, probe_a).unwrap();

            h.merge_clock(lc(probe_b, 1, 1));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 1, 1)));

            // Sanity check just the clock tick
            h.merge_clock(lc(probe_b, 1, 2));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 1, 2)));

            // Sanity check the epoch tick
            h.merge_clock(lc(probe_b, 2, 2));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 2, 2)));

            // Can't roll back the clock
            h.merge_clock(lc(probe_b, 2, 1));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 2, 2)));

            // Can't roll back the epoch
            h.merge_clock(lc(probe_b, 1, 3));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 2, 2)));

            // Go to the very edge of the epoch's range
            let emax = ProbeEpoch::MAX;
            let tmax = ProbeTicks::MAX;
            h.merge_clock(lc(probe_b, emax.0, tmax.0));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, emax.0, tmax.0)));

            // Wraparound to 1 is now allowed
            h.merge_clock(lc(probe_b, 1, 1));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 1, 1)));
        }

        // Wrap around can happen even if a few messages were missed (because of
        // repeated restarts)
        {
            let mut storage_a = [0u8; 512];
            let h = DynamicHistory::new_at(&mut storage_a, probe_a).unwrap();

            h.merge_clock(lc(probe_b, ProbeEpoch::MAX.0 - 2, 1));
            h.merge_clock(lc(probe_b, 2, 1));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 2, 1)));
        }

        // But not outside the threshold
        {
            let mut storage_a = [0u8; 512];
            let h = DynamicHistory::new_at(&mut storage_a, probe_a).unwrap();

            h.merge_clock(lc(probe_b, ProbeEpoch::MAX.0 - 2, 1));
            h.merge_clock(lc(probe_b, 5, 1));
            assert_eq!(
                find_clock(&h, probe_b),
                Some(lc(probe_b, ProbeEpoch::MAX.0 - 2, 1))
            );
        }
    }

    #[test]
    fn merged_clocks_overflow_error_event() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut storage = [0u8; 512];
        let h = DynamicHistory::new_at(&mut storage, probe_id).unwrap();

        let lc = |id: ProbeId, epoch: u16, clock: u16| LogicalClock {
            id,
            epoch: ProbeEpoch(epoch),
            ticks: ProbeTicks(clock),
        };

        assert!(h.clocks.capacity() * 4 <= core::u16::MAX as usize);
        for i in 1..h.clocks.capacity() * 4 {
            let other_probe = ProbeId::new(i as u32).unwrap();
            h.merge_clock(lc(other_probe, 0, i as u16));
        }

        // Make sure we've filled up the clocks
        assert_eq!(h.clocks.len(), h.clocks.capacity());

        // When we generate a report, it should contain the merged clocks overflow event
        let mut report_dest = [0_u8; 512];
        let bytes_written = h.report(&mut report_dest).unwrap();
        let log_report = WireReport::new(&report_dest[..bytes_written]).unwrap();

        assert_eq!(log_report.n_clocks() as usize, h.clocks.capacity());
        assert_eq!(log_report.n_log_entries(), 17);

        let offset = log_report.n_clocks() as usize * size_of::<LogicalClock>();
        let log_bytes = &log_report.payload()[offset..];

        let found_internal_event = log_bytes
            .chunks_exact(size_of::<LogEntry>())
            .map(|bytes| crate::wire::le_bytes::read_u32(bytes))
            .map(|word| unsafe { LogEntry::new_unchecked(word) })
            .find(|log_entry| {
                if let Some(ev) = log_entry.interpret_as_event_id() {
                    if ev == EventId::EVENT_NUM_CLOCKS_OVERFLOWED {
                        assert!(!log_entry.has_event_with_payload_bit_set());
                        assert!(!log_entry.has_clock_bit_set());
                        return true;
                    }
                }
                false
            });
        assert_eq!(
            found_internal_event,
            Some(LogEntry::event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED))
        );
    }
}
