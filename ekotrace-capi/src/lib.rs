#![no_std]
#![feature(lang_items, core_intrinsics)]
#![allow(clippy::not_unsafe_ptr_arg_deref)]
pub use ekotrace_capi_impl::{
    CausalSnapshot, ChunkedReportToken, Ekotrace, EkotraceError, EkotraceInstant,
};

#[no_mangle]
pub extern "C" fn ekotrace_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    tracer_id: u32,
    out: *mut *mut Ekotrace<'static>,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_initialize(destination, destination_size_bytes, tracer_id, out)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_record_event(tracer, event_id) }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: u32,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload) }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_i8(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: i8,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload as _)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_u8(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: u8,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, u32::from(payload))
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_i16(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: i16,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload as _)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_u16(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: u16,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, u32::from(payload))
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_i32(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: i32,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload as _)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_u32(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: u32,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload) }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_bool(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: bool,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, u32::from(payload))
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event_with_payload_f32(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
    payload: f32,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_record_event_with_payload(tracer, event_id, payload.to_bits())
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_report(
    tracer: *mut Ekotrace<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_report(
            tracer,
            log_report_destination,
            log_report_destination_size_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_distribute_snapshot(
    tracer: *mut Ekotrace<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_distribute_snapshot(
            tracer,
            history_destination,
            history_destination_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_distribute_fixed_size_snapshot(
    tracer: *mut Ekotrace<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_distribute_fixed_size_snapshot(tracer, destination_snapshot)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_merge_snapshot(
    tracer: *mut Ekotrace<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_merge_snapshot(tracer, history_source, history_source_bytes)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_merge_fixed_size_snapshot(
    tracer: *mut Ekotrace<'static>,
    snapshot: *const CausalSnapshot,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_merge_fixed_size_snapshot(tracer, snapshot) }
}
#[no_mangle]
pub extern "C" fn ekotrace_now(tracer: *mut Ekotrace<'static>) -> EkotraceInstant {
    unsafe { ekotrace_capi_impl::ekotrace_now(tracer) }
}

#[no_mangle]
pub extern "C" fn ekotrace_start_chunked_report(
    tracer: *mut Ekotrace<'static>,
    out_report_token: *mut ChunkedReportToken,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_start_chunked_report(tracer, out_report_token) }
}

#[no_mangle]
pub extern "C" fn ekotrace_write_next_report_chunk(
    tracer: *mut Ekotrace<'static>,
    report_token: *const ChunkedReportToken,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceError {
    unsafe {
        ekotrace_capi_impl::ekotrace_write_next_report_chunk(
            tracer,
            report_token,
            log_report_destination,
            log_report_destination_size_bytes,
            out_written_bytes,
        )
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_finish_chunked_report(
    tracer: *mut Ekotrace<'static>,
    report_token: *const ChunkedReportToken,
) -> EkotraceError {
    unsafe { ekotrace_capi_impl::ekotrace_finish_chunked_report(tracer, report_token) }
}

#[cfg(not(test))]
#[panic_handler]
pub fn ekotrace_default_panic_abort(_info: &core::panic::PanicInfo) -> ! {
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
