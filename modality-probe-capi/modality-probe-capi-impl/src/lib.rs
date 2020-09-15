#![no_std]

use modality_probe::*;
pub use modality_probe::{
    next_sequence_id_fn, CausalSnapshot, ModalityProbe, ModalityProbeInstant,
};

pub type ModalityProbeError = usize;
/// Everything went fine
pub const MODALITY_PROBE_ERROR_OK: ModalityProbeError = 0;
/// A null pointer was provided to the function
pub const MODALITY_PROBE_ERROR_NULL_POINTER: ModalityProbeError = 1;
/// An event id outside of the allowed range was provided.
pub const MODALITY_PROBE_ERROR_INVALID_EVENT_ID: ModalityProbeError = 2;
/// A probe id outside of the allowed range was provided.
pub const MODALITY_PROBE_ERROR_INVALID_PROBE_ID: ModalityProbeError = 3;
/// The size available for output bytes was insufficient
/// to store a valid representation.
pub const MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES: ModalityProbeError = 4;
/// Bumped into a pointer size limitation
pub const MODALITY_PROBE_ERROR_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE: ModalityProbeError = 5;
/// The local probe does not have enough space to track all
/// of direct neighbors attempting to communicate with it.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS: ModalityProbeError = 6;
/// The the external history source buffer we attempted to merge
/// was insufficiently sized for a valid causal snapshot.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_INSUFFICIENT_SOURCE_BYTES: ModalityProbeError = 7;
/// The provided external history violated a semantic rule of the protocol;
/// such as by having a probe_id out of the allowed value range.
/// Detected during merging.
pub const MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS: ModalityProbeError = 8;

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
    probe_id: u32,
    next_sequence_id: Option<next_sequence_id_fn>,
    next_sequence_id_user_state: *mut core::ffi::c_void,
    out: *mut *mut ModalityProbe<'static>,
) -> ModalityProbeError {
    if destination.is_null() {
        return MODALITY_PROBE_ERROR_NULL_POINTER;
    }
    if destination_size_bytes < core::mem::size_of::<ModalityProbe<'static>>() {
        return MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES;
    }
    let restart_counter_provider = if let Some(iface) = next_sequence_id {
        RestartCounterProvider::C(CRestartCounterProvider {
            iface,
            state: next_sequence_id_user_state,
        })
    } else {
        RestartCounterProvider::NoRestartTracking
    };
    match ModalityProbe::try_initialize_at(
        core::slice::from_raw_parts_mut(destination, destination_size_bytes),
        probe_id,
        restart_counter_provider,
    ) {
        Ok(t) => {
            *out = t;
            MODALITY_PROBE_ERROR_OK
        }
        Err(InitializationError::InvalidProbeId) => MODALITY_PROBE_ERROR_INVALID_PROBE_ID,
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
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match probe.try_record_event(event_id) {
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
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match probe.try_record_event_with_payload(event_id, payload) {
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
    probe: *mut ModalityProbe<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    if log_report_destination.is_null() {
        return MODALITY_PROBE_ERROR_NULL_POINTER;
    }
    match probe.report(core::slice::from_raw_parts_mut(
        log_report_destination,
        log_report_destination_size_bytes,
    )) {
        Ok(b) => {
            *out_written_bytes = b.map(|nonzero| nonzero.get()).unwrap_or(0);
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => report_error_to_modality_probe_error(e),
    }
}

fn report_error_to_modality_probe_error(report_error: ReportError) -> ModalityProbeError {
    match report_error {
        ReportError::InsufficientDestinationSize => {
            MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
    }
}

fn produce_error_to_modality_probe_error(produce_error: ProduceError) -> ModalityProbeError {
    match produce_error {
        ProduceError::InsufficientDestinationSize => {
            MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES
        }
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_produce_snapshot(
    probe: *mut ModalityProbe<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    *destination_snapshot = probe.produce_snapshot();
    MODALITY_PROBE_ERROR_OK
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_produce_snapshot_bytes(
    probe: *mut ModalityProbe<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    if history_destination.is_null() {
        return MODALITY_PROBE_ERROR_NULL_POINTER;
    }
    match probe.produce_snapshot_bytes(core::slice::from_raw_parts_mut(
        history_destination,
        history_destination_bytes,
    )) {
        Ok(written_bytes) => {
            *out_written_bytes = written_bytes;
            MODALITY_PROBE_ERROR_OK
        }
        Err(e) => produce_error_to_modality_probe_error(e),
    }
}

fn merge_error_to_modality_probe_error(merge_error: MergeError) -> ModalityProbeError {
    match merge_error {
        MergeError::ExceededAvailableClocks => MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS,
        MergeError::InsufficientSourceSize => MODALITY_PROBE_ERROR_INSUFFICIENT_SOURCE_BYTES,
        MergeError::ExternalHistorySemantics => {
            MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS
        }
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_merge_snapshot(
    probe: *mut ModalityProbe<'static>,
    snapshot: *const CausalSnapshot,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    let snapshot = &*snapshot;
    if ProbeId::new(snapshot.clock.id.get_raw()).is_none() {
        MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS
    } else {
        match probe.merge_snapshot(snapshot) {
            Ok(_) => MODALITY_PROBE_ERROR_OK,
            Err(e) => merge_error_to_modality_probe_error(e),
        }
    }
}

/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_merge_snapshot_bytes(
    probe: *mut ModalityProbe<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> ModalityProbeError {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => return MODALITY_PROBE_ERROR_NULL_POINTER,
    };
    match probe.merge_snapshot_bytes(core::slice::from_raw_parts(
        history_source,
        history_source_bytes,
    )) {
        Ok(_) => MODALITY_PROBE_ERROR_OK,
        Err(e) => merge_error_to_modality_probe_error(e),
    }
}

/// Capture the ModalityProbe instance's moment in causal time
/// for correlation with external systems.
///
/// If the pointer to the ModalityProbe instance was null,
/// returns an `ModalityProbeInstant` with its `clock.id` value
/// set to the invalid probe id `0`.
///
/// # Safety
///
/// The ModalityProbe instance pointer must be non-null and point
/// to an initialized instance operating in a single-threaded
/// fashion.
#[allow(invalid_value)]
#[cfg_attr(feature = "no_mangle", no_mangle)]
pub unsafe fn modality_probe_now(probe: *mut ModalityProbe<'static>) -> ModalityProbeInstant {
    let probe = match probe.as_mut() {
        Some(t) => t,
        None => {
            return ModalityProbeInstant {
                clock: LogicalClock {
                    // This is intentionally generating an invalid value,
                    // per the documentation above
                    id: core::mem::transmute(0u32),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                event_count: 0,
            };
        }
    };
    probe.now()
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::MaybeUninit;

    fn stack_snapshot(probe: *mut ModalityProbe<'static>) -> CausalSnapshot {
        let mut snap = MaybeUninit::uninit();
        assert_eq!(MODALITY_PROBE_ERROR_OK, unsafe {
            modality_probe_produce_snapshot(probe, snap.as_mut_ptr())
        });
        unsafe { snap.assume_init() }
    }

    #[test]
    fn end_to_end_use_of_modality_probe_capi_works() {
        let mut backend = [0u8; 2099];

        let probe_id = 2;
        let mut storage = [0u8; 1024];
        let storage_slice = &mut storage;
        let mut probe = MaybeUninit::uninit();
        let result = unsafe {
            modality_probe_initialize(
                storage_slice.as_mut_ptr() as *mut u8,
                storage_slice.len(),
                probe_id,
                None,
                core::ptr::null_mut(),
                probe.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        let probe = unsafe { probe.assume_init() };
        let snap_empty = stack_snapshot(probe);
        assert_eq!(snap_empty.clock.id.get_raw(), probe_id);
        unsafe {
            modality_probe_record_event(probe, 100);
        }
        let snap_a = stack_snapshot(probe);
        assert!(snap_empty < snap_a);
        assert!(!(snap_a < snap_empty));

        assert!(&backend.iter().all(|b| *b == 0));
        let mut bytes_written: usize = 0;
        let result = unsafe {
            modality_probe_report(
                probe,
                backend.as_mut_ptr(),
                backend.len(),
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        assert!(bytes_written > 0);
        assert!(!&backend.iter().all(|b| *b == 0));

        unsafe {
            modality_probe_record_event(probe, 100);
        }
        let mut bytes_written: usize = 0;
        let result = unsafe {
            modality_probe_report(
                probe,
                (&mut backend[..6]).as_mut_ptr(),
                6,
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES, result);
        assert_eq!(bytes_written, 0);

        let snap_b = stack_snapshot(probe);
        // We expect the local clock to have progressed thanks to recording an event
        // internally when we successfully transmitted the state to the backend.
        assert!(snap_a < snap_b);
        assert!(!(snap_b < snap_a));
        let snap_b_neighborhood = stack_snapshot(probe);
        assert!(snap_b < snap_b_neighborhood);

        // Share that snapshot with another component in the system, pretend it lives on
        // some other thread.
        let remote_probe_id = probe_id + 1;

        let mut remote_storage = [0u8; 1024];
        let remote_storage_slice = &mut remote_storage;
        let mut remote_probe = MaybeUninit::uninit();
        let result = unsafe {
            modality_probe_initialize(
                remote_storage_slice.as_mut_ptr() as *mut u8,
                remote_storage_slice.len(),
                remote_probe_id,
                None,
                core::ptr::null_mut(),
                remote_probe.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, result);
        let remote_probe = unsafe { remote_probe.assume_init() };
        let remote_snap_pre_merge = stack_snapshot(remote_probe);
        // Since we haven't manually combined history information yet, the remote's
        // history is disjoint
        assert_eq!(
            None,
            remote_snap_pre_merge.partial_cmp(&snap_b_neighborhood)
        );
        assert!(!(snap_b_neighborhood < remote_snap_pre_merge));
        assert_eq!(remote_snap_pre_merge.clock.id.get_raw(), remote_probe_id);

        unsafe {
            modality_probe_merge_snapshot(
                remote_probe,
                &snap_b_neighborhood as *const CausalSnapshot,
            )
        };

        let remote_snap_post_merge = stack_snapshot(remote_probe);
        assert!(!(remote_snap_post_merge < snap_b_neighborhood));

        let snap_c = stack_snapshot(probe);
        assert!(snap_b < snap_c);
        assert!(!(snap_c < snap_b));
    }
}
