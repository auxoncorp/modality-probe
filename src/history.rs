use core::{
    cmp,
    convert::TryFrom,
    mem::{align_of, size_of, MaybeUninit},
    num::NonZeroUsize,
};

use fixed_slice_vec::{
    single::{EmbedValueError, SplitUninitError},
    FixedSliceVec, StorageError,
};
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

use fenced_ring_buffer::{FencedRingBuffer, WholeEntry};

use crate::{
    log::{LogBuffer, LogEntry},
    restart_counter::RestartCounterProvider,
    wire::{report::WireReport, WireCausalSnapshot},
    CausalSnapshot, EventId, LogicalClock, MergeError, ModalityProbeInstant, OrdClock, ProbeEpoch,
    ProbeId, ProbeTicks, ProduceError, ReportError, RestartCounter, StorageSetupError,
};

pub const MIN_CLOCKS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_CLOCKS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + 3 * size_of::<u32>()
    + MIN_CLOCKS_LEN * size_of::<LogicalClock>()
    + MIN_LOG_LEN * size_of::<LogEntry>();

// Struct alignment is the maximum alignment of
// all of its fields, thus we're 8-byte aligned
const_assert_eq!(align_of::<u64>(), align_of::<DynamicHistory>());

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
    size_of::<u32>()
        + size_of::<ProbeId>()
        + size_of::<LogBuffer<'_>>()
        + size_of::<u32>()
        + size_of::<LogicalClock>()
        + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<RestartCounterProvider<'_>>()
        + size_of::<u64>(),
    size_of::<DynamicHistory>()
);

// 4 bytes of padding required before clocks list to get FixedSliceVec to 8 byte align
#[cfg(target_pointer_width = "64")]
const_assert_eq!(
    size_of::<u32>()
        + size_of::<ProbeId>()
        + size_of::<LogBuffer<'_>>()
        + size_of::<u32>()
        + size_of::<LogicalClock>()
        + 4
        + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<RestartCounterProvider<'_>>()
        + size_of::<u64>(),
    size_of::<DynamicHistory>()
);

/// Manages the core of a probe in-memory implementation
/// backed by runtime-sized arrays of current logical clocks
/// and probe log items
///
/// Note: overwrite_priority, probe_id, and log must be accessed by the debug collector using direct memory access.
/// No non-repr(C) fields or usizes (including refs or slices) should be put before those fields,
/// as that would result in the offsets of those fields to change depending on the architecture of the target.
#[derive(Debug)]
#[repr(C)]
pub struct DynamicHistory<'a> {
    /// Minimum priority level of items that can be written to the log
    pub(crate) overwrite_priority: u32,
    /// ID of this probe
    pub(crate) probe_id: ProbeId,
    /// Log used to store events and trace clocks
    pub(crate) log: LogBuffer<'a>,
    /// The number of events seen since the current
    /// probe's logical clock last increased.
    pub(crate) event_count: u32,
    pub(crate) self_clock: LogicalClock,
    /// Invariants:
    ///   * The first clock is always that of the local probe id
    pub(crate) clocks: FixedSliceVec<'a, LogicalClock>,
    pub(crate) restart_counter: RestartCounterProvider<'a>,
    pub(crate) report_seq_num: u64,
}

#[derive(Debug)]
struct ClocksFullError;

impl<'a> DynamicHistory<'a> {
    #[inline]
    pub(crate) fn new_at(
        destination: &'a mut [MaybeUninit<u8>],
        probe_id: ProbeId,
        restart_counter: RestartCounterProvider<'a>,
    ) -> Result<&'a mut DynamicHistory<'a>, StorageSetupError> {
        let remaining_bytes = destination.len();
        if remaining_bytes < MIN_HISTORY_SIZE_BYTES {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        if destination.as_ptr().is_null() {
            return Err(StorageSetupError::NullDestination);
        }
        let history =
            match fixed_slice_vec::single::embed_uninit(destination, |dynamic_region_slice| {
                DynamicHistory::new(dynamic_region_slice, probe_id, restart_counter)
            }) {
                Ok(v) => Ok(v),
                Err(EmbedValueError::SplitUninitError(SplitUninitError::InsufficientSpace)) => {
                    Err(StorageSetupError::UnderMinimumAllowedSize)
                }
                Err(EmbedValueError::SplitUninitError(SplitUninitError::Unalignable)) => {
                    Err(StorageSetupError::UnderMinimumAllowedSize)
                }
                Err(EmbedValueError::SplitUninitError(
                    SplitUninitError::ZeroSizedTypesUnsupported,
                )) => {
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
        dynamic_region_slice: &'a mut [MaybeUninit<u8>],
        probe_id: ProbeId,
        mut restart_counter: RestartCounterProvider<'a>,
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
        let mut clocks = FixedSliceVec::from_uninit_bytes(clocks_region);
        // Create new FencedRingBuffer, using full log region instead of rounding to power of 2 length for
        // optimized indexing
        // Note: point of future improvement - a heuristic could be used to determine whether or not the memory cost
        // of rounding the log's storage space outweighs the runtime cost of using mod operations for indexing
        let log = FencedRingBuffer::new_from_uninit_bytes(log_region, false)
            .map_err(|_| StorageSetupError::UnderMinimumAllowedSize)?;
        if clocks.capacity() < MIN_CLOCKS_LEN || (log.capacity() as usize) < MIN_LOG_LEN {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        let (initial_epoch, restart_counter_had_error) =
            DynamicHistory::calculate_next_epoch(&mut restart_counter, probe_id, None);
        clocks
            .try_push(LogicalClock {
                id: probe_id,
                epoch: initial_epoch,
                ticks: ProbeTicks(0),
            })
            .expect(
                "The History.clocks field should always contain a clock for this probe instance",
            );
        let mut history = DynamicHistory {
            overwrite_priority: 0,
            report_seq_num: 0,
            event_count: 0,
            self_clock: LogicalClock {
                id: probe_id,
                epoch: initial_epoch,
                ticks: ProbeTicks(0),
            },
            probe_id,
            clocks,
            log,
            restart_counter,
        };
        history.write_clocks_to_log(&[history.self_clock]);
        history.record_event(EventId::EVENT_PROBE_INITIALIZED);
        if restart_counter_had_error.0 {
            history.record_event(EventId::EVENT_INVALID_NEXT_EPOCH_SEQ_ID);
        }
        Ok(history)
    }

    #[inline]
    fn merge_overwritten_clock(&mut self, overwritten: Option<WholeEntry<LogEntry>>) {
        if let Some(WholeEntry::Double(one, two)) = overwritten {
            // If what we get out of the log is a clock, merge it into clocks list
            if one.has_clock_bit_set() {
                if let Some(id) = ProbeId::new(one.interpret_as_logical_clock_probe_id()) {
                    let (epoch, ticks) = crate::unpack_clock_word(two.raw());
                    self.merge_clock(LogicalClock { id, epoch, ticks });
                }
            }
        }
    }

    /// Isolated function for figuring out what the next epoch should be for the probe.
    fn calculate_next_epoch(
        restart_counter: &mut RestartCounterProvider,
        probe_id: ProbeId,
        prior_epoch: Option<ProbeEpoch>,
    ) -> (ProbeEpoch, RestartCounterProvidedInvalidEpochSeqId) {
        if restart_counter.is_tracking_restarts() {
            if let Ok(next_persistent_sequence_epoch) = restart_counter.next_sequence_id(probe_id) {
                (
                    ProbeEpoch(next_persistent_sequence_epoch),
                    RestartCounterProvidedInvalidEpochSeqId(false),
                )
            } else {
                (
                    ProbeEpoch::MIN,
                    RestartCounterProvidedInvalidEpochSeqId(true),
                )
            }
        } else if let Some(prior_epoch) = prior_epoch {
            (
                ProbeEpoch(prior_epoch.0.wrapping_add(1)),
                RestartCounterProvidedInvalidEpochSeqId(false),
            )
        } else {
            (
                ProbeEpoch::MIN,
                RestartCounterProvidedInvalidEpochSeqId(false),
            )
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
        let overwritten = self.log.push(LogEntry::event(event_id));
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
        let (first, second) = LogEntry::event_with_payload(event_id, payload);
        let (first_overwritten, second_overwritten) = self.log.push_double(first, second);
        self.merge_overwritten_clock(first_overwritten);
        self.merge_overwritten_clock(second_overwritten);
        self.event_count = self.event_count.saturating_add(1);
    }

    /// Increments the clock in the logical clock corresponding to this probe instance
    #[inline]
    fn increment_local_clock(&mut self) {
        let original_epoch = self.self_clock.epoch;
        let did_overflow = self.self_clock.increment();
        self.event_count = 0;

        if did_overflow {
            let (fresh_epoch, restart_counter_had_error) = DynamicHistory::calculate_next_epoch(
                &mut self.restart_counter,
                self.probe_id,
                Some(original_epoch),
            );
            self.self_clock.epoch = fresh_epoch;
            self.record_event_with_payload(
                EventId::EVENT_LOGICAL_CLOCK_OVERFLOWED,
                self.self_clock.epoch.0 as u32,
            );
            if restart_counter_had_error.0 {
                self.record_event(EventId::EVENT_INVALID_NEXT_EPOCH_SEQ_ID);
            }
        }
    }

    #[inline]
    pub(crate) fn now(&self) -> ModalityProbeInstant {
        ModalityProbeInstant {
            clock: self.self_clock,
            event_count: self.event_count,
        }
    }

    pub(crate) fn report(
        &mut self,
        destination: &mut [u8],
    ) -> Result<Option<NonZeroUsize>, ReportError> {
        // The log has been drained if there are no events report
        // (excluding the expected EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
        match self.log.len() {
            0 => return Ok(None),
            1 => {
                if let Some(WholeEntry::Single(peeked_entry)) = self.log.peek() {
                    if peeked_entry.interpret_as_event_id()
                        == Some(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                    {
                        return Ok(None);
                    }
                }
            }
            _ => (),
        }

        // If we can't store at least a header and one event, it's a hard error
        if destination.len() < WireReport::<&[u8]>::buffer_len(0, 1) {
            return Err(ReportError::InsufficientDestinationSize);
        }

        let self_clock = self.self_clock;
        let mut report = WireReport::new_unchecked(destination);
        report.set_fingerprint();
        report.set_probe_id(self.probe_id);
        report.set_clock(crate::pack_clock_word(self_clock.epoch, self_clock.ticks));
        report.set_persistent_epoch_counting(self.restart_counter.is_tracking_restarts());

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
            let (clocks_region, log_region) =
                payload.split_at_mut(self.clocks.len() * size_of::<LogicalClock>());
            for (c, dest_bytes) in self
                .clocks
                .iter()
                .zip(clocks_region.chunks_exact_mut(size_of::<LogicalClock>()))
            {
                let (first, second) = LogEntry::clock(*c);
                dest_bytes[0..4].copy_from_slice(&first.raw().to_le_bytes());
                dest_bytes[4..8].copy_from_slice(&second.raw().to_le_bytes());
            }

            let clocks = &mut self.clocks;
            let mut did_clocks_overflow = false;
            let mut n_copied = 0;

            // Round num_missed to fit into a u32
            let n_entries_missed = u64::min(self.log.num_missed(), u32::MAX as u64) as u32;
            if n_entries_missed != 0 {
                // Log missed entries event
                let (first, second) =
                    LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, n_entries_missed);
                let dest_bytes = &mut log_region[0..2 * size_of::<LogEntry>()];
                dest_bytes[0..4].copy_from_slice(&first.raw().to_le_bytes());
                dest_bytes[4..8].copy_from_slice(&second.raw().to_le_bytes());
                n_copied += 2;
            }

            let n_entries_possible = log_region.len() / size_of::<LogEntry>();
            // We peek the next entry so that we never throw away an item we don't have space for,
            // since the size of the next entry isn't known until it is peeked
            while let Some(peeked) = self.log.peek() {
                match peeked {
                    WholeEntry::Double(first, second) => {
                        if n_copied > n_entries_possible - 2 {
                            // Not enough space for the double-item entry, break
                            // out of the loop here, and don't consume the peeked entries
                            break;
                        }

                        // Merge clocks into probe's clock list
                        if first.has_clock_bit_set() {
                            // Safe to unwrap because entry was written into the log as a clock probe id
                            let id =
                                ProbeId::new(first.interpret_as_logical_clock_probe_id()).unwrap();
                            let (epoch, ticks) = crate::unpack_clock_word(second.raw());
                            if Self::merge_clocks(clocks, LogicalClock { id, epoch, ticks })
                                .is_err()
                            {
                                did_clocks_overflow = true;
                            }
                        }

                        let dest_bytes = &mut log_region[n_copied * size_of::<LogEntry>()
                            ..(n_copied + 2) * size_of::<LogEntry>()];
                        dest_bytes[0..4].copy_from_slice(&first.raw().to_le_bytes());
                        dest_bytes[4..8].copy_from_slice(&second.raw().to_le_bytes());
                        n_copied += 2;
                    }
                    WholeEntry::Single(entry) => {
                        if n_copied > n_entries_possible - 1 {
                            // Not enough space for the entry, break out of the loop
                            // here, and don't consume the peeked entry
                            break;
                        }
                        let dest_bytes = &mut log_region[n_copied * size_of::<LogEntry>()
                            ..(n_copied + 1) * size_of::<LogEntry>()];
                        dest_bytes.copy_from_slice(&entry.raw().to_le_bytes());
                        n_copied += 1;
                    }
                }
                // We have already included this entry in the report, so it is safe to pop from the log
                let consumed_entry = self.log.pop();
                debug_assert_eq!(consumed_entry, Some(peeked));
            }

            report.set_n_log_entries(n_copied as u32);

            if did_clocks_overflow {
                self.record_event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED);
            }
        }

        self.report_seq_num = self.report_seq_num.wrapping_add(1);
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);

        Ok(NonZeroUsize::new(
            WireReport::<&[u8]>::header_len() + report.payload_len(),
        ))
    }

    #[inline]
    pub(crate) fn produce_snapshot(&mut self) -> CausalSnapshot {
        let snap = CausalSnapshot {
            clock: self.self_clock,
            reserved_0: [0, 0],
            reserved_1: [0, 0],
        };
        self.increment_local_clock();
        self.write_clocks_to_log(&[self.self_clock]);
        snap
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
        s.set_reserved_0([0, 0]);
        s.set_reserved_1([0, 0]);
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
        if external_id == self.probe_id {
            // Quietly ignore self-snapshots in order to reduce complexity
            // around divergence between the self-clock and the frontier set
            // and to allow self-clocks in the log to remain the canonical
            // logical-segment transition point.
            return Ok(());
        }
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
            let (first, second) = LogEntry::clock(*c);
            let (first_overwritten, second_overwritten) = self.log.push_double(first, second);
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
    ) -> Result<(), StorageError<LogicalClock>> {
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

struct RestartCounterProvidedInvalidEpochSeqId(bool);

#[cfg(test)]
mod test {
    use super::*;
    use crate::restart_counter::RestartSequenceIdUnavailable;
    use crate::{RestartCounter, RustRestartCounterProvider};

    struct PersistentRestartProvider {
        next_seq_id: u16,
        count: usize,
    }

    impl RestartCounter for PersistentRestartProvider {
        fn next_sequence_id(
            &mut self,
            _probe_id: ProbeId,
        ) -> Result<u16, RestartSequenceIdUnavailable> {
            let next = self.next_seq_id;
            self.next_seq_id = next.wrapping_add(1);
            self.count += 1;
            Ok(next)
        }
    }

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
            let mut storage_a = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(
                &mut storage_a,
                probe_a,
                RestartCounterProvider::NoRestartTracking,
            )
            .unwrap();

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
            let mut storage_a = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(
                &mut storage_a,
                probe_a,
                RestartCounterProvider::NoRestartTracking,
            )
            .unwrap();

            h.merge_clock(lc(probe_b, ProbeEpoch::MAX.0 - 2, 1));
            h.merge_clock(lc(probe_b, 2, 1));
            assert_eq!(find_clock(&h, probe_b), Some(lc(probe_b, 2, 1)));
        }

        // But not outside the threshold
        {
            let mut storage_a = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(
                &mut storage_a,
                probe_a,
                RestartCounterProvider::NoRestartTracking,
            )
            .unwrap();

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
        let mut storage = [MaybeUninit::new(0u8); 512];
        let h = DynamicHistory::new_at(
            &mut storage,
            probe_id,
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

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
        let bytes_written = h.report(&mut report_dest).unwrap().unwrap();
        let log_report = WireReport::new(&report_dest[..bytes_written.get()]).unwrap();

        assert_eq!(log_report.n_clocks() as usize, h.clocks.capacity());
        assert_eq!(log_report.n_log_entries(), 20);

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

    #[test]
    fn drain_report_until_completion() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let h = DynamicHistory::new_at(
            &mut storage,
            probe_id,
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        for i in 0..h.log.capacity() {
            h.record_event(EventId::new(i as u32 + 1).unwrap());
        }
        assert_eq!(h.log.len(), h.log.capacity());

        const EXPECTED_LOG_CAPACITY: usize = 196;
        assert_eq!(h.log.capacity(), EXPECTED_LOG_CAPACITY);

        // Each report (excluding the first, and until drained) adds an
        // extra internal event: EventId::EVENT_PRODUCED_EXTERNAL_REPORT.
        const EXPECTED_LOG_ENTRIES: usize = EXPECTED_LOG_CAPACITY + 6;

        // Drain into a buffer that is ~1/4 of the log buffer capacity
        let report_buffer_size =
            WireReport::<&[u8]>::buffer_len(h.clocks.len(), h.log.capacity() / 4);
        let mut report_dest = vec![0_u8; report_buffer_size];

        let mut reported_log_entries = 0;

        // First four reports should be filled to buffer capacity
        for _ in 0..4 {
            let bytes_written = h.report(&mut report_dest).unwrap().unwrap();
            assert_eq!(bytes_written.get(), report_buffer_size);
            let log_report = WireReport::new(&report_dest[..bytes_written.get()]).unwrap();
            assert_eq!(log_report.n_clocks() as usize, h.clocks.len());
            assert_eq!(log_report.n_log_entries(), 49);
            reported_log_entries += log_report.n_log_entries() as usize;
        }

        // One more to get the remainder
        let bytes_written = h.report(&mut report_dest).unwrap().unwrap();
        assert_eq!(bytes_written.get(), 59);
        let log_report = WireReport::new(&report_dest[..bytes_written.get()]).unwrap();
        assert_eq!(log_report.n_clocks() as usize, h.clocks.len());
        assert_eq!(log_report.n_log_entries(), 6);
        reported_log_entries += log_report.n_log_entries() as usize;

        assert_eq!(reported_log_entries, EXPECTED_LOG_ENTRIES);

        // The log has been drained, always returns zero bytes until
        // something gets pushed to the log
        for _ in 0..10 {
            let bytes_written = h.report(&mut report_dest).unwrap();
            assert_eq!(bytes_written, None);
        }

        // A new entry means more data to report
        h.record_event(EventId::new(1234).unwrap());
        let bytes_written = h.report(&mut report_dest).unwrap().unwrap();
        let log_report = WireReport::new(&report_dest[..bytes_written.get()]).unwrap();
        assert_eq!(log_report.n_clocks() as usize, h.clocks.len());
        // 2: EventId::EVENT_PRODUCED_EXTERNAL_REPORT + user event
        assert_eq!(log_report.n_log_entries(), 2);
    }

    #[test]
    fn persistent_epoch() {
        let probe_a = ProbeId::new(1).unwrap();

        let mut next_id_provider = PersistentRestartProvider {
            next_seq_id: 100,
            count: 0,
        };

        // When a probe is tracking restarts, then it gets the initial epoch portion
        // of the clock from the implementation
        {
            let provider = RestartCounterProvider::Rust(RustRestartCounterProvider {
                iface: &mut next_id_provider,
            });

            let mut storage_a = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(&mut storage_a, probe_a, provider).unwrap();

            let now = h.now();
            assert_eq!(now.clock.epoch.0, 100);
            assert_eq!(now.clock.ticks.0, 0);
        }
        assert_eq!(next_id_provider.next_seq_id, 101);
        assert_eq!(next_id_provider.count, 1);

        {
            let provider = RestartCounterProvider::Rust(RustRestartCounterProvider {
                iface: &mut next_id_provider,
            });

            let mut storage_a = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(&mut storage_a, probe_a, provider).unwrap();

            let now = h.now();
            assert_eq!(now.clock.epoch.0, 101);
            assert_eq!(now.clock.ticks.0, 0);

            // Go to the very edge of the clock's range
            h.self_clock.ticks = ProbeTicks::MAX;
            let now = h.now();
            assert_eq!(now.clock.epoch.0, 101);
            assert_eq!(now.clock.ticks, ProbeTicks::MAX);

            // Bump the clock, triggering an overflow
            h.increment_local_clock();

            // The overflow should have caused another sequence id retrieval
            let now = h.now();
            assert_eq!(now.clock.epoch.0, 102);
            assert_eq!(now.clock.ticks.0, 1);
        }
        assert_eq!(next_id_provider.next_seq_id, 103);
        assert_eq!(next_id_provider.count, 3);
    }

    #[test]
    fn misbehaving_persistent_epoch_event() {
        struct MisbehavingRestartProvider {}
        impl RestartCounter for MisbehavingRestartProvider {
            fn next_sequence_id(
                &mut self,
                _probe_id: ProbeId,
            ) -> Result<u16, RestartSequenceIdUnavailable> {
                Err(RestartSequenceIdUnavailable)
            }
        }

        let mut next_id_provider = MisbehavingRestartProvider {};
        let provider = RestartCounterProvider::Rust(RustRestartCounterProvider {
            iface: &mut next_id_provider,
        });

        let probe_id = ProbeId::new(1).unwrap();
        let mut storage = [MaybeUninit::new(0u8); 512];
        let h = DynamicHistory::new_at(&mut storage, probe_id, provider).unwrap();

        let now = h.now();
        assert_eq!(now.clock.epoch, ProbeEpoch::MIN);
        assert_eq!(now.clock.ticks, ProbeTicks::MIN);

        let mut found_error_event_count = 0;
        while let Some(entry) = h.log.pop() {
            match entry {
                WholeEntry::Single(entry)
                    if entry.interpret_as_event_id()
                        == Some(EventId::EVENT_INVALID_NEXT_EPOCH_SEQ_ID) =>
                {
                    found_error_event_count += 1;
                }
                _ => (),
            }
        }
        assert_eq!(1, found_error_event_count);
    }

    mod now_tests {
        use super::*;
        #[test]
        fn produce_and_merge_snapshot_ticks_clock() {
            let probe_id = ProbeId::new(1).unwrap();
            let mut storage = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(
                &mut storage,
                probe_id,
                RestartCounterProvider::NoRestartTracking,
            )
            .unwrap();
            let epoch = ProbeEpoch(0);

            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(0)
                    },
                    event_count: 1
                }
            );

            let local_snap_a = h.produce_snapshot();
            assert_eq!(
                local_snap_a,
                CausalSnapshot {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(0)
                    },
                    reserved_0: [0, 0],
                    reserved_1: [0, 0]
                }
            );
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(1)
                    },
                    event_count: 0
                }
            );

            let local_snap_b = h.produce_snapshot();
            assert_eq!(
                &local_snap_b,
                &CausalSnapshot {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(1)
                    },
                    reserved_0: [0, 0],
                    reserved_1: [0, 0]
                }
            );
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(2)
                    },
                    event_count: 0
                }
            );

            let remote_probe_id = ProbeId::new(probe_id.get_raw() + 1).unwrap();
            let remote_snap = CausalSnapshot {
                clock: LogicalClock {
                    id: remote_probe_id,
                    epoch,
                    ticks: ProbeTicks(2),
                },
                reserved_0: [0, 0],
                reserved_1: [0, 0],
            };
            h.merge_snapshot(&remote_snap).unwrap();
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(3)
                    },
                    event_count: 0
                }
            );
        }
        #[test]
        fn record_events_ticks_event_counts() {
            let probe_id = ProbeId::new(1).unwrap();
            let mut storage = [MaybeUninit::new(0u8); 512];
            let h = DynamicHistory::new_at(
                &mut storage,
                probe_id,
                RestartCounterProvider::NoRestartTracking,
            )
            .unwrap();
            let epoch = ProbeEpoch(0);

            // event_count starts at 1 because of the EventId::EVENT_PROBE_INITIALIZED event
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(0)
                    },
                    event_count: 1
                }
            );
            let event_id = EventId::new(456).unwrap();
            h.record_event(event_id);
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(0)
                    },
                    event_count: 2
                }
            );
            for _ in 0..8 {
                h.record_event(event_id);
            }
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(0)
                    },
                    event_count: 10
                }
            );

            // A produce-induced clock tick resets the event count
            let _ = h.produce_snapshot();
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(1)
                    },
                    event_count: 0
                }
            );
            h.record_event(event_id);
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(1)
                    },
                    event_count: 1
                }
            );

            // A merge-induced clock tick resets the event count
            let remote_probe_id = ProbeId::new(probe_id.get_raw() + 1).unwrap();
            let remote_snap = CausalSnapshot {
                clock: LogicalClock {
                    id: remote_probe_id,
                    epoch,
                    ticks: ProbeTicks(2),
                },
                reserved_0: [0, 0],
                reserved_1: [0, 0],
            };
            h.merge_snapshot(&remote_snap).unwrap();
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(2)
                    },
                    event_count: 0
                }
            );
            h.record_event(event_id);
            assert_eq!(
                h.now(),
                ModalityProbeInstant {
                    clock: LogicalClock {
                        id: probe_id,
                        epoch,
                        ticks: ProbeTicks(2)
                    },
                    event_count: 1
                }
            );
        }
    }
}
