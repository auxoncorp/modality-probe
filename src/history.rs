use super::{
    CausalSnapshot, EventId, LogicalClock, MergeError, ModalityProbeInstant, ProbeId, ProduceError,
    StorageSetupError,
};
use crate::compact_log::{CompactLogItem, CompactLogVec};
use crate::report::chunked::ChunkedReportState;
use core::cmp::{max, Ordering, PartialEq};
use core::fmt::{Error as FmtError, Formatter};
use core::mem::{align_of, size_of};
use fixed_slice_vec::single::{embed, EmbedValueError, SplitUninitError};
use fixed_slice_vec::FixedSliceVec;
use static_assertions::{assert_eq_align, assert_eq_size, const_assert, const_assert_eq};

impl core::fmt::Debug for CausalSnapshot {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "CausalSnapshot {{ id: {:?}, count: {} }}",
            self.clock.id, self.clock.count,
        )
    }
}

/// Do a logical clock comparison, ignoring the source probe_id
impl PartialEq for CausalSnapshot {
    fn eq(&self, other: &Self) -> bool {
        self.clock == other.clock
    }
}

impl PartialOrd for CausalSnapshot {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.clock.id != other.clock.id {
            None
        } else {
            self.clock.count.partial_cmp(&other.clock.count)
        }
    }
}

pub const MIN_CLOCKS_LEN: usize = 2;
pub const MIN_LOG_LEN: usize = MIN_CLOCKS_LEN * 16;
pub const MIN_HISTORY_SIZE_BYTES: usize = size_of::<DynamicHistory>()
    + 3 * size_of::<u32>()
    + MIN_CLOCKS_LEN * size_of::<LogicalClock>()
    + MIN_LOG_LEN * size_of::<CompactLogItem>();

const_assert_eq!(align_of::<usize>(), align_of::<DynamicHistory>());
const_assert_eq!(4, align_of::<LogicalClock>());
const_assert_eq!(4, align_of::<CompactLogItem>());

assert_eq_size!(u64, LogicalClock);
assert_eq_align!(u32, LogicalClock);

assert_eq_size!(u32, CompactLogItem);
assert_eq_align!(u32, CompactLogItem);

const_assert_eq!(12, size_of::<CausalSnapshot>());
const_assert_eq!(4, align_of::<CausalSnapshot>());

const_assert_eq!(12, size_of::<ModalityProbeInstant>());
const_assert_eq!(4, align_of::<ModalityProbeInstant>());

const_assert_eq!(
    10 + size_of::<FixedSliceVec<'_, LogicalClock>>()
        + size_of::<CompactLogVec<'_>>()
        + size_of::<ChunkedReportState>(),
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
    pub(crate) chunked_report_state: ChunkedReportState,
    /// Invariants:
    ///   * The first clock is always that of the local probe id
    pub(crate) clocks: FixedSliceVec<'a, LogicalClock>,
    /// Invariants:
    ///   * This log must always contain at least one item
    ///   * The first group of items in the log must always be logical clocks,
    /// starting with the local logical clock.
    pub(crate) compact_log: CompactLogVec<'a>,
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
        let history = match embed(destination, |dynamic_region_slice| {
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
                    <= history.compact_log.as_slice().as_ptr() as usize,
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
        let max_n_clocks = max(
            MIN_CLOCKS_LEN,
            dynamic_region_slice.len() / 8 / size_of::<LogicalClock>(),
        );
        let clocks_region_bytes = max_n_clocks * size_of::<LogicalClock>();
        if clocks_region_bytes > dynamic_region_slice.len() {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        let (clocks_region, log_region) = dynamic_region_slice.split_at_mut(clocks_region_bytes);
        let mut clocks = FixedSliceVec::from_bytes(clocks_region);
        let mut compact_log = CompactLogVec::from_bytes(log_region);
        if clocks.capacity() < MIN_CLOCKS_LEN || compact_log.capacity() < MIN_LOG_LEN {
            return Err(StorageSetupError::UnderMinimumAllowedSize);
        }
        clocks
            .try_push(LogicalClock {
                id: probe_id,
                count: 0,
            })
            .expect(
                "The History.clocks field should always contain a clock for this probe instance",
            );
        // This ensures that the first log segment always has a piece of logical
        // clock information.
        DynamicHistory::write_clocks_to_log(&mut compact_log, clocks.as_slice());
        Ok(DynamicHistory {
            probe_id,
            clocks,
            compact_log,
            chunked_report_state: ChunkedReportState::default(),
            event_count: 0,
        })
    }

    /// Add an item to the internal log that records this event
    /// occurred.
    ///
    /// Note: This function silently drop events if the log has
    /// overflowed or if the instance is locked for reporting.
    #[inline]
    pub(crate) fn record_event(&mut self, event_id: EventId) {
        if self.chunked_report_state.is_report_in_progress() {
            return;
        }
        let len = self.compact_log.len();
        let cap = self.compact_log.capacity();
        if len == cap {
            return;
        }
        // N.B. point for future improvement - basic compression here
        if self
            .compact_log
            .try_push(CompactLogItem::event(event_id))
            .is_ok()
        {
            self.event_count = self.event_count.saturating_add(1);
        }
    }

    /// Add the event and its payload to the internal log, recording
    /// that this event occurred.
    ///
    /// Note: This function silently drop events if the log has
    /// overflowed or if the instance is locked for reporting.
    #[inline]
    pub(crate) fn record_event_with_payload(&mut self, event_id: EventId, payload: u32) {
        if self.chunked_report_state.is_report_in_progress() {
            return;
        }
        let len = self.compact_log.len();
        let cap = self.compact_log.capacity();
        // Room for two?
        if len + 1 >= cap {
            return;
        }
        let (ev, payload) = CompactLogItem::event_with_payload(event_id, payload);
        if self.compact_log.try_push(ev).is_err() {
            return;
        }
        if self.compact_log.try_push(payload).is_ok() {
            self.event_count = self.event_count.saturating_add(1);
        }
    }

    /// Increments the clock in the logical clock corresponding to this probe instance
    #[inline]
    fn increment_local_clock_count(&mut self) {
        // N.B. We rely on the fact that the first member of the clocks
        // collection is always the clock for this probe
        debug_assert!(self.probe_id == self.clocks[0].id);
        debug_assert!(
            !self.chunked_report_state.is_report_in_progress(),
            "Should not be incrementing the local clock count when a report is in progress"
        );
        self.clocks.as_mut_slice()[0].count = self.clocks.as_slice()[0].count.saturating_add(1);
        self.event_count = 0;
    }

    /// Produce a transparent but limited snapshot of the causal state for transmission
    /// within the system under test
    #[inline]
    pub(crate) fn produce_snapshot(&mut self) -> Result<CausalSnapshot, ProduceError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(ProduceError::ReportLockConflict);
        }
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        Ok(CausalSnapshot {
            clock: self.clocks[0],
            reserved_0: 0,
            reserved_1: 0,
        })
    }

    /// Merge a publicly-transmittable causal history into our specialized local in-memory storage
    #[inline]
    pub(crate) fn merge_snapshot(
        &mut self,
        external_history: &CausalSnapshot,
    ) -> Result<(), MergeError> {
        if self.chunked_report_state.is_report_in_progress() {
            return Err(MergeError::ReportLockConflict);
        }
        self.merge_internal(external_history.clock.id, external_history.clock.count)
    }

    #[inline]
    fn merge_internal(
        &mut self,
        external_id: ProbeId,
        external_clock: u32,
    ) -> Result<(), MergeError> {
        // Ensure that there is a clock for the neighbor that sent the snapshot
        if !self.clocks.as_slice().iter().any(|b| b.id == external_id)
            && self
                .clocks
                .try_push(LogicalClock {
                    id: external_id,
                    count: 0,
                })
                .is_err()
        {
            let _ = self
                .compact_log
                .try_push(CompactLogItem::event(EventId::EVENT_NUM_CLOCKS_OVERFLOWED));
            return Err(MergeError::ExceededAvailableClocks);
        }
        if external_clock != 0 {
            for internal_clock in self.clocks.as_mut_slice() {
                // N.B This depends on the local clock already having been created, above,
                // when we received a history from the clock's source probe_id.
                // During early probe event recording, may cause us to drop
                // data from an indirect neighbor that
                // is also a direct neighbor (but has not yet sent us a message).
                if internal_clock.id == external_id {
                    internal_clock.count = max(internal_clock.count, external_clock);
                    break;
                }
            }
        }
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        Ok(())
    }

    #[inline]
    fn write_clocks_to_log<'d>(compact_log: &mut CompactLogVec<'d>, clocks: &[LogicalClock]) {
        if compact_log.is_full() {
            return;
        }
        let max_len_that_can_fit_a_clock_and_overflow_notice =
            (compact_log.capacity() - 2) as usize;
        let mut log_len = compact_log.len();
        let mut has_overflowed_log = false;
        for b in clocks {
            let (id, count) = CompactLogItem::clock(*b);
            if log_len < max_len_that_can_fit_a_clock_and_overflow_notice {
                compact_log
                    .try_push(id)
                    .expect("Already checked id will fit");
                compact_log
                    .try_push(count)
                    .expect("Already checked count will fit");
                log_len += 2;
            } else {
                // TODO - instead of breaking in the middle, should we have just not written
                // any of the logical clock at all?
                has_overflowed_log = true;
                break;
            }
        }
        if has_overflowed_log {
            let _ = compact_log.try_push(CompactLogItem::event(EventId::EVENT_LOG_OVERFLOWED));
        }
    }

    #[inline]
    fn write_current_clocks_to_log(&mut self) {
        let clocks = self.clocks.as_slice();
        let log = &mut self.compact_log;
        DynamicHistory::write_clocks_to_log(log, clocks);
    }

    pub(crate) fn finished_report_logging(&mut self) {
        self.compact_log.clear();
        self.increment_local_clock_count();
        self.write_current_clocks_to_log();
        self.record_event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT);
    }

    pub(crate) fn now(&self) -> ModalityProbeInstant {
        ModalityProbeInstant {
            clock: self.clocks[0],
            event_count: self.event_count,
        }
    }
}
