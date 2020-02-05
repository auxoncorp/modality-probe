#![no_std]
#![feature(lang_items, core_intrinsics)]
pub use ekotrace_capi_impl::{CausalSnapshot, Ekotrace, EkotraceInstant, EkotraceResult};

#[no_mangle]
pub extern "C" fn ekotrace_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    tracer_id: u32,
    out: *mut *mut Ekotrace<'static>,
) -> EkotraceResult {
    unsafe {
        ekotrace_capi_impl::ekotrace_initialize(destination, destination_size_bytes, tracer_id, out)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_record_event(
    tracer: *mut Ekotrace<'static>,
    event_id: u32,
) -> EkotraceResult {
    unsafe { ekotrace_capi_impl::ekotrace_record_event(tracer, event_id) }
}

#[no_mangle]
pub extern "C" fn ekotrace_report(
    tracer: *mut Ekotrace<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
    out_written_bytes: *mut usize,
) -> EkotraceResult {
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
) -> EkotraceResult {
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
) -> EkotraceResult {
    unsafe {
        ekotrace_capi_impl::ekotrace_distribute_fixed_size_snapshot(tracer, destination_snapshot)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_merge_snapshot(
    tracer: *mut Ekotrace<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> EkotraceResult {
    unsafe {
        ekotrace_capi_impl::ekotrace_merge_snapshot(tracer, history_source, history_source_bytes)
    }
}

#[no_mangle]
pub extern "C" fn ekotrace_merge_fixed_size_snapshot(
    tracer: *mut Ekotrace<'static>,
    snapshot: *const CausalSnapshot,
) -> EkotraceResult {
    unsafe { ekotrace_capi_impl::ekotrace_merge_fixed_size_snapshot(tracer, snapshot) }
}
#[no_mangle]
pub extern "C" fn ekotrace_now(tracer: *mut Ekotrace<'static>) -> EkotraceInstant {
    unsafe { ekotrace_capi_impl::ekotrace_now(tracer) }
}

#[cfg(not(test))]
#[panic_handler]
pub fn ekotrace_default_panic_abort(_info: &core::panic::PanicInfo) -> ! {
    // N.B. Point for future expansion - could use feature flagging here
    // to pull in libc_print for operating systems that support it.
    // A separate alternative would be to provide a hook for
    // setting a panic-handler implementation at runtime.
    unsafe {
        core::intrinsics::abort();
    }
}

#[cfg(not(test))]
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {
    unsafe {
        core::intrinsics::abort();
    }
}
