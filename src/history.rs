use core::{
    cmp,
    convert::TryFrom,
    mem::{align_of, size_of},
};

use fixed_slice_vec::{
    single::{EmbedValueError, SplitUninitError},
    FixedSliceVec, TryPushError,
};
use race_buffer::writer::OverwrittenEntry;
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

use crate::{
    log::{LogEntry, RaceLog},
    payload::{write_report_payload, FrontierClocksFSV, PayloadOutputByteSlice},
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

#[cfg(target_pointer_width = "32")]
const_assert_eq!(
    size_of::<ProbeId>()
        + size_of::<u32>()
        + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<LogicalClock>()
        + size_of::<RaceLog<'_>>()
        + size_of::<usize>()
        + size_of::<u64>(),
    size_of::<DynamicHistory>()
);

#[cfg(not(target_pointer_width = "32"))]
const_assert_eq!(
    size_of::<ProbeId>()
        + size_of::<u32>()
        + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<LogicalClock>()
        + size_of::<RaceLog<'_>>()
        + size_of::<u64>()
        + size_of::<u64>(),
    size_of::<DynamicHistory>()
);

/// Manages the core of a probe in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and probe log items
#[derive(Debug)]
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
    pub(crate) read_cursor: u64,
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
                    <= history.log.get_slice().as_ptr() as usize,
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
        // Create new racebuffer, using full log region instead of rounding to power of 2 length for
        // optimized indexing
        // Note: point of future improvement - a heuristic could be used to determine whether or not the memory cost
        // of rounding the log's storage space outweighs the runtime cost of using mod operations for indexing
        let log = RaceLog::new_from_bytes(log_region, false)
            .map_err(|_| StorageSetupError::UnderMinimumAllowedSize)?;
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
            read_cursor: 0,
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
    fn merge_overwritten_clock(&mut self, overwritten: OverwrittenEntry<LogEntry>) {
        if let OverwrittenEntry::Double(one, two) = overwritten {
            // If what we get out of the log is a clock, merge it into clocks list
            if one.has_clock_bit_set() {
                if let Some(id) = ProbeId::new(one.interpret_as_logical_clock_probe_id()) {
                    let (epoch, ticks) = crate::unpack_clock_word(two.raw());
                    self.merge_clock(LogicalClock { id, epoch, ticks });
                }
            }
        }
    }

    #[inline]
    fn write_to_log(&mut self, entry: LogEntry) {
        let overwritten = self.log.write(entry);
        self.merge_overwritten_clock(overwritten);
    }

    #[inline]
    fn write_double_to_log(&mut self, prefix: LogEntry, suffix: LogEntry) {
        let (first_overwritten, second_overwritten) = self.log.write_double(prefix, suffix);
        self.merge_overwritten_clock(first_overwritten);
        self.merge_overwritten_clock(second_overwritten);
    }

    /// Add an item to the internal log that records this event
    /// occurred.
    ///
    /// Note: this function overwrites older events in the log if it
    /// is full.
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        // N.B. point for future improvement - basic compression here
        self.write_to_log(LogEntry::event(event_id));
        self.event_count = self.event_count.saturating_add(1);
    }

    /// Add the event and its payload to the internal log, recording
    /// that this event occurred.
    ///
    /// Note: this function overwrites older events in the log if it
    /// is full.
    #[inline]
    pub(crate) fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        let (ev, pay) = LogEntry::event_with_payload(event_id, payload);
        self.write_double_to_log(ev, pay);
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

            let mut payload = report.payload_mut();
            let (n_items_written, n_items_read, did_clocks_overflow) = write_report_payload(
                self.log.iter(self.read_cursor),
                &mut FrontierClocksFSV::new(&mut self.clocks),
                &mut PayloadOutputByteSlice::new(&mut payload),
            );
            // Buffer cannot store more than u32::MAX/2 items, so n_items_written will always fit into u32
            report.set_n_log_entries(n_items_written as u32);

            // Wrapping add
            // Buffer cannot store more than u32::MAX/2 items, so n_items_read will always fit into u32
            self.read_cursor += n_items_read as u64; 
            if did_clocks_overflow {
                self.record_event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED);
            }
        }

        self.report_seq_num = self.report_seq_num.wrapping_add(1);
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);

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
            let (probe_id, clock) = LogEntry::clock(*c);
            self.write_double_to_log(probe_id, clock);
        }
    }

    fn merge_clock(&mut self, ext_clock: LogicalClock) {
        if Self::merge_clocks(&mut self.clocks, ext_clock).is_err() {
            self.record_event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED);
        }
    }

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
}
