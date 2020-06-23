#![no_std]
#![feature(lang_items, core_intrinsics)]
#![allow(clippy::not_unsafe_ptr_arg_deref)]
pub use modality_probe_capi_impl::{
    CausalSnapshot, ChunkedReportToken, ModalityProbe, ModalityProbeError, ModalityProbeInstant,
};

#[no_mangle]
pub extern "C" fn modality_probe_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    probe_id: u32,
    out: *mut *mut ModalityProbe<'static>,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_initialize(
            destination,
            destination_size_bytes,
            probe_id,
            out,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_record_event(
    probe: *mut ModalityProbe<'static>,
    event_id: u32,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_record_event(probe, event_id) }
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
pub extern "C" fn modality_probe_distribute_snapshot(
    probe: *mut ModalityProbe<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_distribute_snapshot(
            probe,
            history_destination,
            history_destination_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_distribute_fixed_size_snapshot(
    probe: *mut ModalityProbe<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_distribute_fixed_size_snapshot(
            probe,
            destination_snapshot,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_snapshot(
    probe: *mut ModalityProbe<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_merge_snapshot(
            probe,
            history_source,
            history_source_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_merge_fixed_size_snapshot(
    probe: *mut ModalityProbe<'static>,
    snapshot: *const CausalSnapshot,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_merge_fixed_size_snapshot(probe, snapshot) }
}
#[no_mangle]
pub extern "C" fn modality_probe_now(probe: *mut ModalityProbe<'static>) -> ModalityProbeInstant {
    unsafe { modality_probe_capi_impl::modality_probe_now(probe) }
}

#[no_mangle]
pub extern "C" fn modality_probe_start_chunked_report(
    probe: *mut ModalityProbe<'static>,
    out_report_token: *mut ChunkedReportToken,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_start_chunked_report(probe, out_report_token)
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_write_next_report_chunk(
    probe: *mut ModalityProbe<'static>,
    report_token: *const ChunkedReportToken,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> ModalityProbeError {
    unsafe {
        modality_probe_capi_impl::modality_probe_write_next_report_chunk(
            probe,
            report_token,
            log_report_destination,
            log_report_destination_size_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn modality_probe_finish_chunked_report(
    probe: *mut ModalityProbe<'static>,
    report_token: *const ChunkedReportToken,
) -> ModalityProbeError {
    unsafe { modality_probe_capi_impl::modality_probe_finish_chunked_report(probe, report_token) }
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
