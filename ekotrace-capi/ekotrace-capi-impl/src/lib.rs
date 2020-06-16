#![no_std]
use ekotrace::report::chunked::ChunkedReportError;
pub use ekotrace::report::chunked::ChunkedReportToken;
use ekotrace::*;
pub use ekotrace::{CausalSnapshot, Ekotrace, EkotraceInstant};

pub type EkotraceResult = usize;
/// Everything went fine
pub const EKOTRACE_RESULT_OK: EkotraceResult = 0;
/// A null pointer was provided to the function
pub const EKOTRACE_RESULT_NULL_POINTER: EkotraceResult = 1;
/// An event id outside of the allowed range was provided.
pub const EKOTRACE_RESULT_INVALID_EVENT_ID: EkotraceResult = 2;
/// A tracer id outside of the allowed range was provided.
pub const EKOTRACE_RESULT_INVALID_TRACER_ID: EkotraceResult = 3;
/// The size available for output bytes was insufficient
/// to store a valid representation.
pub const EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES: EkotraceResult = 4;
/// Bumped into a pointer size limitation
pub const EKOTRACE_RESULT_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE: EkotraceResult = 5;
/// An unexpected error in internal data encoding occurred.
pub const EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR: EkotraceResult = 6;
/// The local tracer does not have enough space to track all
/// of direct neighbors attempting to communicate with it.
/// Detected during merging.
pub const EKOTRACE_RESULT_EXCEEDED_AVAILABLE_CLOCKS: EkotraceResult = 7;

/// The external history we attempted to merge was encoded
/// in an invalid fashion.
/// Detected during merging.
pub const EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_ENCODING: EkotraceResult = 8;
/// The provided external history violated a semantic rule of the protocol;
/// such as by having a tracer_id out of the allowed value range.
/// Detected during merging.
pub const EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS: EkotraceResult = 9;
/// The tracer encountered a problem dealing with extension metadata
pub const EKOTRACE_RESULT_EXTENSION_ERROR: EkotraceResult = 10;
/// The tracer attempted to mutate internal state while
/// a report lock was active.
pub const EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR: EkotraceResult = 11;
/// The tracer attempted to do a chunked report operation when no
/// chunked report has been started.
pub const EKOTRACE_RESULT_NO_CHUNKED_REPORT_IN_PROGRESS: EkotraceResult = 12;

/// # Safety
///
/// No other part of the program should manipulate
/// the contents of `destination` region. The Ekotrace instance
/// provided in the out-pointer should be used in a single-
/// threaded fashion.
///
/// If the function returns any result besides EKOTRACE_RESULT_OK,
/// there has been an error, and the out-pointer for the Ekotrace instance
/// will not be populated.
///
/// The contents of the `destination` region are not guaranteed
/// in the case of an error result.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    tracer_id: u32,
    out: *mut *mut Ekotrace<'static>,
) -> EkotraceResult {
    if destination.is_null() {
        return EKOTRACE_RESULT_NULL_POINTER;
    }
    if destination_size_bytes < core::mem::size_of::<Ekotrace<'static>>() {
        return EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES;
    }
    match Ekotrace::try_initialize_at(
        core::slice::from_raw_parts_mut(destination, destination_size_bytes),
        tracer_id,
    ) {
        Ok(t) => {
            *out = t;
            EKOTRACE_RESULT_OK
        }
        Err(InitializationError::InvalidTracerId) => EKOTRACE_RESULT_INVALID_TRACER_ID,
        Err(InitializationError::StorageSetupError(StorageSetupError::NullDestination)) => {
            EKOTRACE_RESULT_NULL_POINTER
        }
        Err(InitializationError::StorageSetupError(StorageSetupError::UnderMinimumAllowedSize)) => {
            EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(InitializationError::StorageSetupError(
            StorageSetupError::ExceededMaximumAddressableSize,
        )) => EKOTRACE_RESULT_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE,
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_record_event(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.try_record_event(event_id) {
        Ok(_) => EKOTRACE_RESULT_OK,
        Err(ekotrace::InvalidEventId) => EKOTRACE_RESULT_INVALID_EVENT_ID,
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_record_event_with_payload(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: u32,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.try_record_event_with_payload(event_id, payload) {
        Ok(_) => EKOTRACE_RESULT_OK,
        Err(ekotrace::InvalidEventId) => EKOTRACE_RESULT_INVALID_EVENT_ID,
    }
}

/// Write a bulk report to the supplied byte destination.
///
/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_report(
    tracer: *mut Ekotrace<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    if log_report_destination.is_null() {
        return EKOTRACE_RESULT_NULL_POINTER;
    }
    let written_bytes = match tracer.report(core::slice::from_raw_parts_mut(
        log_report_destination,
        log_report_destination_size_bytes,
    )) {
        Ok(b) => b,
        Err(ReportError::InsufficientDestinationSize) => {
            return EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(ReportError::Encoding) => return EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR,
        Err(ReportError::Extension) => return EKOTRACE_RESULT_EXTENSION_ERROR,
        Err(ReportError::ReportLockConflict) => return EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR,
    };

    *out_written_bytes = written_bytes;
    EKOTRACE_RESULT_OK
}

fn report_error_to_ekotrace_result(report_error: ReportError) -> EkotraceResult {
    match report_error {
        ReportError::InsufficientDestinationSize => EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES,
        ReportError::Encoding => EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR,
        ReportError::Extension => EKOTRACE_RESULT_EXTENSION_ERROR,
        ReportError::ReportLockConflict => EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_distribute_snapshot(
    tracer: *mut Ekotrace<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.distribute_snapshot(core::slice::from_raw_parts_mut(
        history_destination,
        history_destination_bytes,
    )) {
        Ok(written_bytes) => {
            *out_written_bytes = written_bytes;
            EKOTRACE_RESULT_OK
        }
        Err(e) => distribute_error_to_ekotrace_result(e),
    }
}

fn distribute_error_to_ekotrace_result(distribute_error: DistributeError) -> EkotraceResult {
    match distribute_error {
        DistributeError::InsufficientDestinationSize => {
            EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES
        }
        DistributeError::Encoding => EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR,
        DistributeError::Extension => EKOTRACE_RESULT_EXTENSION_ERROR,
        DistributeError::ReportLockConflict => EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_distribute_fixed_size_snapshot(
    tracer: *mut Ekotrace<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.distribute_fixed_size_snapshot() {
        Ok(snapshot) => {
            *destination_snapshot = snapshot;
            EKOTRACE_RESULT_OK
        }
        Err(e) => distribute_error_to_ekotrace_result(e),
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_merge_snapshot(
    tracer: *mut Ekotrace<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.merge_snapshot(core::slice::from_raw_parts(
        history_source,
        history_source_bytes,
    )) {
        Ok(_) => EKOTRACE_RESULT_OK,
        Err(e) => merge_error_to_ekotrace_result(e),
    }
}

fn merge_error_to_ekotrace_result(merge_error: MergeError) -> EkotraceResult {
    match merge_error {
        MergeError::ExceededAvailableClocks => EKOTRACE_RESULT_EXCEEDED_AVAILABLE_CLOCKS,
        MergeError::ExternalHistoryEncoding => EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_ENCODING,
        MergeError::ExternalHistorySemantics => EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS,
        MergeError::Extension => EKOTRACE_RESULT_EXTENSION_ERROR,
        MergeError::ReportLockConflict => EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR,
    }
}

/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_merge_fixed_size_snapshot(
    tracer: *mut Ekotrace<'static>,
    snapshot: *const CausalSnapshot,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.merge_fixed_size_snapshot(&*snapshot) {
        Ok(_) => EKOTRACE_RESULT_OK,
        Err(e) => merge_error_to_ekotrace_result(e),
    }
}

/// Capture the Ekotrace instance's moment in causal time
/// for correlation with external systems.
///
/// If the pointer to the Ekotrace instance (a.k.a. tracer) was null,
/// returns an `EkotraceInstant` with its `clock.id` value
/// set to the invalid location id `0`.
///
/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[allow(invalid_value)]
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_now(tracer: *mut Ekotrace<'static>) -> EkotraceInstant {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => {
            return EkotraceInstant {
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
// ChunkedReportToken is expressed as a uint16_t in ekotrace.h ,
// so let's be extra sure that the sizes and alignment match up
use static_assertions::{assert_eq_align, assert_eq_size};
assert_eq_size!(u16, ChunkedReportToken);
assert_eq_align!(u16, ChunkedReportToken);

/// Prepare to write a chunked report.
///
/// Populates the out-parameter `out_report_token` with
/// a value that will be used to produce the
/// chunks for the report in calls to
/// `ekotrace_write_next_report_chunk` and `ekotrace_finish_chunked_report`
///
/// Once this method has been called, mutating operations on
/// the Ekotrace instance will return
/// `EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR` until all available chunks have
/// been written with  `ekotrace_write_next_report_chunk`
/// and `ekotrace_finish_chunked_report` called.
///
/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// If the function returns any result besides EKOTRACE_RESULT_OK,
/// there has been an error, and the out-pointer for the chunked report token
/// will not be populated.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_start_chunked_report(
    tracer: *mut Ekotrace<'static>,
    out_report_token: *mut ChunkedReportToken,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.start_chunked_report() {
        Ok(token) => {
            *out_report_token = token;
            EKOTRACE_RESULT_OK
        }
        Err(e) => chunked_report_error_to_ekotrace_result(e),
    }
}

fn chunked_report_error_to_ekotrace_result(cre: ChunkedReportError) -> EkotraceResult {
    match cre {
        ChunkedReportError::ReportError(re) => report_error_to_ekotrace_result(re),
        ChunkedReportError::NoChunkedReportInProgress => {
            EKOTRACE_RESULT_NO_CHUNKED_REPORT_IN_PROGRESS
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
/// populated by the `ekotrace_start_chunked_report` call
/// at the start of this chunked report.
///
/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// The destination buffer pointer must be non-null
/// and should have an associated size == 256 bytes.
///
/// If the function returns any result besides EKOTRACE_RESULT_OK,
/// there has been an error and the contents of the report destination
/// are not certain to be initialized or a valid chunk.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_write_next_report_chunk(
    tracer: *mut Ekotrace<'static>,
    report_token: *const ChunkedReportToken,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.write_next_report_chunk(
        &*report_token,
        core::slice::from_raw_parts_mut(log_report_destination, log_report_destination_size_bytes),
    ) {
        Ok(written_bytes) => {
            *out_written_bytes = written_bytes;
            EKOTRACE_RESULT_OK
        }
        Err(e) => chunked_report_error_to_ekotrace_result(e),
    }
}
/// Necessary clean-up and finishing step at the end
/// of iterating through a chunked report.
///
/// The provided ChunkedReportToken should match the value
/// populated by the `ekotrace_start_chunked_report` call
/// at the start of this chunked report.
///
/// # Safety
///
/// The Ekotrace instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
///
/// If the function returns any result besides EKOTRACE_RESULT_OK,
/// there has been an error.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn ekotrace_finish_chunked_report(
    tracer: *mut Ekotrace<'static>,
    report_token: *const ChunkedReportToken,
) -> EkotraceResult {
    let tracer = match tracer.as_mut() {
        Some(t) => t,
        None => return EKOTRACE_RESULT_NULL_POINTER,
    };
    match tracer.finish_chunked_report(core::ptr::read(report_token)) {
        Ok(_) => EKOTRACE_RESULT_OK,
        Err(e) => chunked_report_error_to_ekotrace_result(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::Ordering;
    use core::mem::MaybeUninit;

    fn stack_snapshot(tracer: *mut Ekotrace<'static>) -> CausalSnapshot {
        let mut snap = MaybeUninit::uninit();
        assert_eq!(EKOTRACE_RESULT_OK, unsafe {
            ekotrace_distribute_fixed_size_snapshot(tracer, snap.as_mut_ptr())
        });
        unsafe { snap.assume_init() }
    }

    #[test]
    fn end_to_end_use_of_ekotrace_capi_works() {
        let mut backend = [0u8; 2099];

        let tracer_id = 2;
        let mut storage = [0u8; 1024];
        let storage_slice = &mut storage;
        let mut tracer = MaybeUninit::uninit();
        let result = unsafe {
            ekotrace_initialize(
                storage_slice.as_mut_ptr() as *mut u8,
                storage_slice.len(),
                tracer_id,
                tracer.as_mut_ptr(),
            )
        };
        assert_eq!(EKOTRACE_RESULT_OK, result);
        let tracer = unsafe { tracer.assume_init() };
        let snap_empty = stack_snapshot(tracer);
        assert_eq!(snap_empty.tracer_id, tracer_id);
        assert_eq!(1, snap_empty.clocks_len);
        unsafe {
            ekotrace_record_event(tracer, 100);
        }
        let snap_a = stack_snapshot(tracer);
        assert!(snap_empty < snap_a);
        assert!(!(snap_a < snap_empty));
        assert_eq!(1, snap_a.clocks_len);

        assert!(&backend.iter().all(|b| *b == 0));
        let mut bytes_written: usize = 0;
        let result = unsafe {
            ekotrace_report(
                tracer,
                backend.as_mut_ptr(),
                backend.len(),
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(EKOTRACE_RESULT_OK, result);
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
            ekotrace_initialize(
                remote_storage_slice.as_mut_ptr() as *mut u8,
                remote_storage_slice.len(),
                remote_tracer_id,
                remote_tracer.as_mut_ptr(),
            )
        };
        assert_eq!(EKOTRACE_RESULT_OK, result);
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
            ekotrace_merge_fixed_size_snapshot(
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
