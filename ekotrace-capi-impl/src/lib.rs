#![no_std]
use ekotrace::*;
pub use ekotrace::{CausalSnapshot, Ekotrace};

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
        Err(_) => return EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES,
    };

    *out_written_bytes = written_bytes;
    EKOTRACE_RESULT_OK
}

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
        Err(ShareError::InsufficientDestinationSize) => {
            EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(ShareError::Encoding) => EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR,
    }
}

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
        Err(ShareError::InsufficientDestinationSize) => {
            EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES
        }
        Err(ShareError::Encoding) => EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR,
    }
}

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
        Err(MergeError::ExceededAvailableClocks) => EKOTRACE_RESULT_EXCEEDED_AVAILABLE_CLOCKS,
        Err(MergeError::ExternalHistoryEncoding) => {
            EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_ENCODING
        }
        Err(MergeError::ExternalHistorySemantics) => {
            EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS
        }
    }
}

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
        Err(MergeError::ExceededAvailableClocks) => EKOTRACE_RESULT_EXCEEDED_AVAILABLE_CLOCKS,
        Err(MergeError::ExternalHistoryEncoding) => {
            EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_ENCODING
        }
        Err(MergeError::ExternalHistorySemantics) => {
            EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS
        }
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

        // Share that snapshot with another component in the system, pretend it lives on some other thread.
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
        // Since we haven't manually combined history information yet, the remote's history is disjoint
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
// TODO - should we expose comparison operations for CausalSnapshot?
// TODO - make tracer size tunable
