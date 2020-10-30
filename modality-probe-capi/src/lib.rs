#![no_std]
#![feature(lang_items, core_intrinsics)]
#![allow(clippy::not_unsafe_ptr_arg_deref)]
use core::mem::MaybeUninit;
pub use modality_probe_capi_impl::{
    next_sequence_id_fn, CausalSnapshot, ModalityProbe, ModalityProbeError, ModalityProbeInstant,
};

#[no_mangle]
pub extern "C" fn modality_probe_initialize(
    destination: *mut MaybeUninit<u8>,
    destination_size_bytes: usize,
    probe_id: u32,
    time_resolution_ns: u32,
    wall_clock_id: u16,
    next_sequence_id: Option<next_sequence_id_fn>,
    next_sequence_id_user_state: *mut core::ffi::c_void,
    out: *mut *mut ModalityProbe<'static>,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_initialize(
            destination,
            destination_size_bytes,
            probe_id,
            time_resolution_ns,
            wall_clock_id,
            next_sequence_id,
            next_sequence_id_user_state,
            out,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_time(
    probe: *mut ModalityProbe<'static>,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_record_time(probe, time_ns) }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_record_event(probe, event_id) }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_time(probe, event_id, time_ns)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(probe, event_id, payload)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe, event_id, payload, time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i8(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i8,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            payload as _,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i8_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i8,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            payload as _,
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u8(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u8,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            u32::from(payload),
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u8_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u8,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            u32::from(payload),
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i16(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i16,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            payload as _,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i16_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i16,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            payload as _,
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u16(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u16,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            u32::from(payload),
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u16_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u16,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            u32::from(payload),
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i32(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i32,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            payload as _,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_i32_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: i32,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            payload as _,
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u32(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(probe, event_id, payload)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_u32_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: u32,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe, event_id, payload, time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_bool(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: bool,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            u32::from(payload),
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_bool_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: bool,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            u32::from(payload),
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_f32(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: f32,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload(
            probe,
            event_id,
            payload.to_bits(),
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event_with_payload_f32_with_time(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
    payload: f32,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_record_event_with_payload_with_time(
            probe,
            event_id,
            payload.to_bits(),
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_report(
    probe: *mut ModalityProbe<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_report(
            probe,
            log_report_destination,
            log_report_destination_size_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_produce_snapshot(
    probe: *mut ModalityProbe<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_produce_snapshot(probe, destination_snapshot)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_produce_snapshot_with_time(
    probe: *mut ModalityProbe<'static>,
    time_ns: u64,
    destination_snapshot: *mut CausalSnapshot,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_produce_snapshot_with_time(
            probe,
            time_ns,
            destination_snapshot,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_produce_snapshot_bytes(
    probe: *mut ModalityProbe<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_produce_snapshot_bytes(
            probe,
            history_destination,
            history_destination_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_produce_snapshot_bytes_with_time(
    probe: *mut ModalityProbe<'static>,
    time_ns: u64,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_produce_snapshot_bytes_with_time(
            probe,
            time_ns,
            history_destination,
            history_destination_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_snapshot(
    probe: *mut ModalityProbe<'static>,
    snapshot: *const CausalSnapshot,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_merge_snapshot(probe, snapshot) }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_snapshot_with_time(
    probe: *mut ModalityProbe<'static>,
    snapshot: *const CausalSnapshot,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_merge_snapshot_with_time(probe, snapshot, time_ns)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_snapshot_bytes(
    probe: *mut ModalityProbe<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_merge_snapshot_bytes(
            probe,
            history_source,
            history_source_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_snapshot_bytes_with_time(
    probe: *mut ModalityProbe<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
    time_ns: u64,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_merge_snapshot_bytes_with_time(
            probe,
            history_source,
            history_source_bytes,
            time_ns,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_now(probe: *mut ModalityProbe<'static>) -> ModalityProbeInstant {
    unsafe { modality_probe_capi_impl::modality_probe_now(probe) }
}

#[cfg(not(test))]
#[panic_handler]
pub fn modality_probe_default_panic_abort(_info: &core::panic::PanicInfo) -> ! {
    // N.B. Point for future expansion - could use feature flagging here
    // to pull in libc_print for operating systems that support it.
    // A separate alternative would be to provide a hook for
    // setting a panic-handler implementation at runtime.
    core::intrinsics::abort();
}

#[cfg(not(test))]
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {
    core::intrinsics::abort();
}
