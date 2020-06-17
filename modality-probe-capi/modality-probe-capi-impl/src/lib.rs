#![no_std]
use modality_probe::report::chunked::ChunkedReportError;
pub use modality_probe::report::chunked::ChunkedReportToken;
use modality_probe::*;
pub use modality_probe::{CausalSnapshot, ModalityProbe, ModalityProbeInstant};

pub type ModalityProbeError = usize;
/// Everything went fine
pub const MODALITY_PROBE_ERROR_OK: ModalityProbeError = 0;
/// A null pointer was provided to the function
pub const MODALITY_PROBE_ERROR_NULL_POINTER: ModalityProbeError = 1;
/// An event id outside of the allowed range was provided.
pub const MODALITY_PROBE_ERROR_INVALID_EVENT_ID: ModalityProbeError = 2;
/// A tracer id outside of the allowed range was provided.
pub const MODALITY_PROBE_ERROR_INVALID_TRACER_ID: ModalityProbeError = 3;
/// The size available for output bytes was insufficient
/// to store a valid representation.
pub const MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES: ModalityProbeError = 4;
/// Bumped into a pointer size limitation
pub const MODALITY_PROBE_ERROR_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE: ModalityProbeError = 5;
/// An unexpected error in internal data encoding occurred.
pub const MODALITY_PROBE_ERROR_INTERNAL_ENCODING_ERROR: ModalityProbeError = 6;
/// The local tracer does not have enough space to track all
/// of direct neighbors attempting to communicate with it.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS: ModalityProbeError = 7;

/// The external history we attempted to merge was encoded
/// in an invalid fashion.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_ENCODING: ModalityProbeError = 8;
/// The provided external history violated a semantic rule of the protocol;
/// such as by having a tracer_id out of the allowed value range.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS: ModalityProbeError = 9;
/// The tracer encountered a problem dealing with extension metadata
pub const MODALITY_PROBE_ERROR_EXTENSION_ERROR: ModalityProbeError = 10;
/// The tracer attempted to mutate internal state while
/// a report lock was active.
pub const MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR: ModalityProbeError = 11;
/// The tracer attempted to do a chunked report operation when no
/// chunked report has been started.
pub const MODALITY_PROBE_ERROR_NO_CHUNKED_REPORT_IN_PROGRESS: ModalityProbeError = 12;

/// # Safety
///
/// No other part of the program should manipulate
/// the contents of `destination` region. The ModalityProbe instance
/// provided in the out-pointer should be used in a single-
/// threaded fashion.
///
/// If the function returns any error besides MODALITY_PROBE_ERROR_OK,
/// there has been an error, and the out-pointer for the ModalityProbe instance
/// will not be populated.
///
/// The contents of the `destination` region are not guaranteed
/// in the case of an error.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    tracer_id: u32,
    out: *mut *mut ModalityProbe<'static>,
) -> ModalityProbeError {
    if destination.is_null() {
        return MODALITY_PROBE_ERROR_NULL_POINTER;
    }
    if destination_size_bytes < core::mem::size_of::<ModalityProbe<'static>>() {
        return MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES;
    }
    match ModalityProbe::try_initialize_at(
        core::slice::from_raw_parts_mut(destination, destination_size_bytes),
        tracer_id,
    ) {
        Ok(t) => {
            *out = t;
            MODALITY_PROBE_ERROR_OK
        }
        Err(InitializationError::InvalidTracerId) => MODALITY_PROBE_ERROR_INVALID_TRACER_ID,
        Err(InitializationError::StorageSetupError(StorageSetupError::NullDestination)) => {
            MODALITY_PROBE_ERROR_NULL_POINTER
        }
        Err(InitializationError::StorageSetupError(StorageSetupError::UnderMinimumAllowedSize)) => {
            MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(InitializationError::StorageSetupError(
            StorageSetupError::ExceededMaximumAddressableSize,
        )) => MODALITY_PROBE_ERROR_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE,
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_record_event(
    tracer: *mut ModalityProbe<'static>,
    event_id: u32,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.try_record_event(event_id) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(modality_probe::InvalidEventId) => MODALITY_PROBE_ERROR_INVALID_EVENT_ID,
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_record_event_with_payload(
    tracer: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.try_record_event_with_payload(event_id, payload) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(modality_probe::InvalidEventId) => MODALITY_PROBE_ERROR_INVALID_EVENT_ID,
    }
}

/// Write a bulk report to the supplied byte destination.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_report(
    tracer: *mut ModalityProbe<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    if log_report_destination.is_null() {
        return MODALITY_PROBE_ERROR_NULL_POINTER;
    }
    let written_bytes = match tracer.report(core::slice::from_raw_parts_mut(
        log_report_destination,
        log_report_destination_size_bytes,
    )) {
        Ok(b) => b,
        Err(ReportError::InsufficientDestinationSize) => {
            return MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(ReportError::Encoding) => return MODALITY_PROBE_ERROR_INTERNAL_ENCODING_ERROR,
        Err(ReportError::Extension) => return MODALITY_PROBE_ERROR_EXTENSION_ERROR,
        Err(ReportError::ReportLockConflict) => {
            return MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR
        }
    };

    *out_written_bytes = written_bytes;
    MODALITY_PROBE_ERROR_OK
}

fn report_error_to_modality_probe_error(report_error: ReportError) -> ModalityProbeError {
    match report_error {
        ReportError::InsufficientDestinationSize => {
            MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
        ReportError::Encoding => MODALITY_PROBE_ERROR_INTERNAL_ENCODING_ERROR,
        ReportError::Extension => MODALITY_PROBE_ERROR_EXTENSION_ERROR,
        ReportError::ReportLockConflict => MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_distribute_snapshot(
    tracer: *mut ModalityProbe<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.distribute_snapshot(core::slice::from_raw_parts_mut(
        history_destination,
        history_destination_bytes,
    )) {
        Ok(written_bytes) => {
            *out_written_bytes = written_bytes;
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => distribute_error_to_modality_probe_error(e),
    }
}

fn distribute_error_to_modality_probe_error(
    distribute_error: DistributeError,
) -> ModalityProbeError {
    match distribute_error {
        DistributeError::InsufficientDestinationSize => {
            MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
        DistributeError::Encoding => MODALITY_PROBE_ERROR_INTERNAL_ENCODING_ERROR,
        DistributeError::Extension => MODALITY_PROBE_ERROR_EXTENSION_ERROR,
        DistributeError::ReportLockConflict => MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_distribute_fixed_size_snapshot(
    tracer: *mut ModalityProbe<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.distribute_fixed_size_snapshot() {
        Ok(snapshot) => {
            *destination_snapshot = snapshot;
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => distribute_error_to_modality_probe_error(e),
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_merge_snapshot(
    tracer: *mut ModalityProbe<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.merge_snapshot(core::slice::from_raw_parts(
        history_source,
        history_source_bytes,
    )) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(e) => merge_error_to_modality_probe_error(e),
    }
}

fn merge_error_to_modality_probe_error(merge_error: MergeError) -> ModalityProbeError {
    match merge_error {
        MergeError::ExceededAvailableClocks => MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS,
        MergeError::ExternalHistoryEncoding => {
            MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_ENCODING
        }
        MergeError::ExternalHistorySemantics => {
            MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS
        }
        MergeError::Extension => MODALITY_PROBE_ERROR_EXTENSION_ERROR,
        MergeError::ReportLockConflict => MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_merge_fixed_size_snapshot(
    tracer: *mut ModalityProbe<'static>,
    snapshot: *const CausalSnapshot,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.merge_fixed_size_snapshot(&*snapshot) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(e) => merge_error_to_modality_probe_error(e),
    }
}

/// Capture the ModalityProbe instance's moment in causal time
/// for correlation with external systems.
///
/// If the pointer to the ModalityProbe instance (a.k.a. tracer) was null,
/// returns an `ModalityProbeInstant` with its `clock.id` value
/// set to the invalid location id `0`.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[allow(invalid_value)]
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_now(tracer: *mut ModalityProbe<'static>) -> ModalityProbeInstant {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => {
            return ModalityProbeInstant {
                clock: LogicalClock {
                    // This is intentionally generating an invalid value,
                    // per the documentation above
                    id: core::mem::transmute(0u32),
                    count: 0,
                },
                event_count: 0,
            };
        }
    };
    tracer.now()
}

// ChunkedReportToken is expressed as a uint16_t in probe.h,
// so let's be extra sure that the sizes and alignment match up
use static_assertions::{assert_eq_align, assert_eq_size};
assert_eq_size!(u16, ChunkedReportToken);
assert_eq_align!(u16, ChunkedReportToken);

/// Prepare to write a chunked report.
///
/// Populates the out-parameter `out_report_token` with
/// a value that will be used to produce the
/// chunks for the report in calls to
/// `modality_probe_write_next_report_chunk` and
/// `modality_probe_finish_chunked_report`
///
/// Once this method has been called, mutating operations on
/// the ModalityProbe instance will return
/// `MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR` until all available chunks
/// have been written with  `modality_probe_write_next_report_chunk`
/// and `modality_probe_finish_chunked_report` called.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// If the function returns any error besides MODALITY_PROBE_ERROR_OK,
/// there has been an error, and the out-pointer for the chunked report token
/// will not be populated.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_start_chunked_report(
    tracer: *mut ModalityProbe<'static>,
    out_report_token: *mut ChunkedReportToken,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.start_chunked_report() {
        Ok(token) => {
            *out_report_token = token;
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => chunked_report_error_to_modality_probe_error(e),
    }
}

fn chunked_report_error_to_modality_probe_error(cre: ChunkedReportError) -> ModalityProbeError {
    match cre {
        ChunkedReportError::ReportError(re) => report_error_to_modality_probe_error(re),
        ChunkedReportError::NoChunkedReportInProgress => {
            MODALITY_PROBE_ERROR_NO_CHUNKED_REPORT_IN_PROGRESS
        }
    }
}
/// Write up to 1 chunk of a report into
/// the provided destination buffer.
///
/// Populates the out-parameter `out_written_bytes` with
/// the number of report bytes written into the destination.
///
/// If the `out_written_bytes` == 0, then no chunk was
/// written and there are no chunks left in the report.
///
/// The provided ChunkedReportToken should match the value
/// populated by the `modality_probe_start_chunked_report` call
/// at the start of this chunked report.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// The destination buffer pointer must be non-null
/// and should have an associated size == 256 bytes.
///
/// If the function returns any error besides MODALITY_PROBE_ERROR_OK,
/// there has been an error and the contents of the report destination
/// are not certain to be initialized or a valid chunk.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_write_next_report_chunk(
    tracer: *mut ModalityProbe<'static>,
    report_token: *const ChunkedReportToken,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.write_next_report_chunk(
        &*report_token,
        core::slice::from_raw_parts_mut(log_report_destination, log_report_destination_size_bytes),
    ) {
        Ok(written_bytes) => {
            *out_written_bytes = written_bytes;
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => chunked_report_error_to_modality_probe_error(e),
    }
}
/// Necessary clean-up and finishing step at the end
/// of iterating through a chunked report.
///
/// The provided ChunkedReportToken should match the value
/// populated by the `modality_probe_start_chunked_report` call
/// at the start of this chunked report.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// If the function returns any error besides MODALITY_PROBE_ERROR_OK,
/// there has been an error.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_finish_chunked_report(
    tracer: *mut ModalityProbe<'static>,
    report_token: *const ChunkedReportToken,
) -> ModalityProbeError {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match tracer.finish_chunked_report(core::ptr::read(report_token)) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(e) => chunked_report_error_to_modality_probe_error(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::Ordering;
    use core::mem::MaybeUninit;

    fn stack_snapshot(tracer: *mut ModalityProbe<'static>) -> CausalSnapshot {
        let mut snap = MaybeUninit::uninit();
        assert_eq!(MODALITY_PROBE_ERROR_OK, unsafe {
            modality_probe_distribute_fixed_size_snapshot(tracer, snap.as_mut_ptr())
        });
        unsafe { snap.assume_init() }
    }

    #[test]
    fn end_to_end_use_of_modality_probe_capi_works() {
        let mut backend = [0u8; 2099];

        let tracer_id = 2;
        let mut storage = [0u8; 1024];
        let storage_slice = &mut storage;
        let mut tracer = MaybeUninit::uninit();
        let result = unsafe {
            modality_probe_initialize(
                storage_slice.as_mut_ptr() as *mut u8,
                storage_slice.len(),
                tracer_id,
                tracer.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        let tracer = unsafe { tracer.assume_init() };
        let snap_empty = stack_snapshot(tracer);
        assert_eq!(snap_empty.tracer_id, tracer_id);
        assert_eq!(1, snap_empty.clocks_len);
        unsafe {
            modality_probe_record_event(tracer, 100);
        }
        let snap_a = stack_snapshot(tracer);
        assert!(snap_empty < snap_a);
        assert!(!(snap_a < snap_empty));
        assert_eq!(1, snap_a.clocks_len);

        assert!(&backend.iter().all(|b| *b == 0));
        let mut bytes_written: usize = 0;
        let result = unsafe {
            modality_probe_report(
                tracer,
                backend.as_mut_ptr(),
                backend.len(),
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        assert!(bytes_written > 0);
        assert!(!&backend.iter().all(|b| *b == 0));
        let snap_b = stack_snapshot(tracer);
        // We expect the local clock to have progressed thanks to recording an event
        // internally when we successfully transmitted the state to the backend.
        assert!(snap_a < snap_b);
        assert!(!(snap_b < snap_a));
        let snap_b_neighborhood = stack_snapshot(tracer);
        assert_eq!(1, snap_b_neighborhood.clocks_len);
        assert!(snap_b < snap_b_neighborhood);

        // Share that snapshot with another component in the system, pretend it lives on
        // some other thread.
        let remote_tracer_id = tracer_id + 1;

        let mut remote_storage = [0u8; 1024];
        let remote_storage_slice = &mut remote_storage;
        let mut remote_tracer = MaybeUninit::uninit();
        let result = unsafe {
            modality_probe_initialize(
                remote_storage_slice.as_mut_ptr() as *mut u8,
                remote_storage_slice.len(),
                remote_tracer_id,
                remote_tracer.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        let remote_tracer = unsafe { remote_tracer.assume_init() };
        let remote_snap_pre_merge = stack_snapshot(remote_tracer);
        // Since we haven't manually combined history information yet, the remote's
        // history is disjoint
        assert_eq!(
            None,
            remote_snap_pre_merge.partial_cmp(&snap_b_neighborhood)
        );
        assert!(!(snap_b_neighborhood < remote_snap_pre_merge));
        assert_eq!(remote_snap_pre_merge.tracer_id, remote_tracer_id);
        assert_eq!(1, remote_snap_pre_merge.clocks_len);

        unsafe {
            modality_probe_merge_fixed_size_snapshot(
                remote_tracer,
                &snap_b_neighborhood as *const CausalSnapshot,
            )
        };

        let remote_snap_post_merge = stack_snapshot(remote_tracer);
        assert_eq!(
            Some(Ordering::Greater),
            remote_snap_post_merge.partial_cmp(&snap_b_neighborhood)
        );
        assert_eq!(
            Some(Ordering::Less),
            snap_b_neighborhood.partial_cmp(&remote_snap_post_merge)
        );
        assert!(snap_b_neighborhood < remote_snap_post_merge);
        assert!(!(remote_snap_post_merge < snap_b_neighborhood));

        let snap_c = stack_snapshot(tracer);
        assert!(snap_b < snap_c);
        assert!(!(snap_c < snap_b));
    }
}
