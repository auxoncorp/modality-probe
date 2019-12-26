#![no_std]
#![feature(lang_items, core_intrinsics)]
use libc::{c_int, c_uchar, c_void, size_t};
use truce::*;
pub use truce::{CausalSnapshot, Tracer};

/// Callback used by C programs to define the work of transmitting
/// trace data to the backend
pub type SendToBackendFn = extern "C" fn(*mut c_void, *const c_uchar, size_t) -> c_int;

#[derive(Debug)]
#[repr(C)]
pub struct TraceBackend {
    pub state: *mut c_void,
    pub send_fn: SendToBackendFn,
}

impl Backend for TraceBackend {
    fn send_tracer_data(&mut self, data: &[u8]) -> bool {
        (self.send_fn)(self.state, data.as_ptr(), data.len()) == 1
    }
}

#[no_mangle]
pub extern "C" fn tracer_initialize(
    destination: *mut u8,
    destination_size_bytes: size_t,
    tracer_id: u32,
    backend: *mut TraceBackend,
) -> *mut Tracer<'static, 'static> {
    assert!(
        !destination.is_null(),
        "tracer destination pointer was null"
    );
    assert!(!backend.is_null(), "tracer backend pointer was null");
    assert!(
        destination_size_bytes >= core::mem::size_of::<Tracer<'static, 'static>>(),
        "insufficient tracer destination bytes to store the tracer"
    );
    unsafe {
        Tracer::initialize_at(
            core::slice::from_raw_parts_mut(destination, destination_size_bytes),
            TracerId::new(tracer_id).expect("tracer_id was zero or over the max allowed value"),
            backend.as_mut().expect("backend pointer was null"),
        )
        .expect("Could not initialize Tracer")
    }
}

#[no_mangle]
pub extern "C" fn tracer_record_event(tracer: *mut Tracer<'static, 'static>, event_id: u32) {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .record_event(EventId::new(event_id).expect("Could not create a non-zero EventId"))
}

#[no_mangle]
pub extern "C" fn tracer_service(tracer: *mut Tracer<'static, 'static>) {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .service()
}

#[no_mangle]
pub extern "C" fn tracer_snapshot(tracer: *mut Tracer<'static, 'static>) -> CausalSnapshot {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .snapshot()
}

#[no_mangle]
pub extern "C" fn tracer_merge_history(
    tracer: *mut Tracer<'static, 'static>,
    snapshot: *const CausalSnapshot,
) {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .merge_history(unsafe { &*snapshot })
}

#[cfg(not(test))]
#[panic_handler]
pub fn panic(_info: &core::panic::PanicInfo) -> ! {
    // N.B. Point for future expansion - could use feature flagging here
    // to pull in libc_print for operating systems that support it
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

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::Ordering;
    use libc::{c_int, c_uchar, c_void, size_t};

    #[derive(Default)]
    struct SendCounter {
        count: usize,
    }
    extern "C" fn send_to_counter_be(
        state: *mut c_void,
        data: *const c_uchar,
        len: size_t,
    ) -> c_int {
        let state_as_counter: &mut SendCounter = unsafe { core::mem::transmute(state) };
        assert!(len > 0);
        assert!(!data.is_null());
        state_as_counter.count += 1;
        1 // ints as bools, yay
    }
    #[test]
    fn end_to_end_use_of_tracer_capi_works() {
        let mut raw_backend = SendCounter::default();
        let be_fn: SendToBackendFn = send_to_counter_be;

        let mut trace_backend = TraceBackend {
            state: &mut raw_backend as *mut SendCounter as *mut c_void,
            send_fn: be_fn,
        };

        let tracer_id = 2;
        let mut storage = [0u8; 1024];
        let storage_slice = &mut storage;
        let tracer = tracer_initialize(
            storage_slice.as_mut_ptr() as *mut u8,
            storage_slice.len(),
            tracer_id,
            &mut trace_backend as *mut TraceBackend,
        );
        let snap_empty = tracer_snapshot(tracer);
        assert_eq!(snap_empty.tracer_id, tracer_id);
        assert_eq!(1, snap_empty.buckets_len);
        tracer_record_event(tracer, 100);
        let snap_a = tracer_snapshot(tracer);
        assert!(snap_empty < snap_a);
        assert!(!(snap_a < snap_empty));
        assert_eq!(1, snap_a.buckets_len);

        assert_eq!(0, raw_backend.count);
        tracer_service(tracer);
        assert_eq!(1, raw_backend.count);
        let snap_b = tracer_snapshot(tracer);
        // We expect the local clock to have progressed thanks to recording an event
        // internally when we successfully transmitted the state to the backend.
        assert!(snap_a < snap_b);
        assert!(!(snap_b < snap_a));
        let snap_b_neighborhood = tracer_snapshot(tracer);
        assert_eq!(1, snap_b_neighborhood.buckets_len);
        assert!(snap_b < snap_b_neighborhood);

        // Share that snapshot with another component in the system, pretend it lives on some other thread.
        let remote_tracer_id = tracer_id + 1;

        let mut remote_storage = [0u8; 1024];
        let remote_storage_slice = &mut remote_storage;
        let remote_tracer = tracer_initialize(
            remote_storage_slice.as_mut_ptr() as *mut u8,
            remote_storage_slice.len(),
            remote_tracer_id,
            &mut trace_backend as *mut TraceBackend,
        );
        let remote_snap_pre_merge = tracer_snapshot(remote_tracer);
        // Since we haven't manually combined history information yet, the remote's history is disjoint
        assert_eq!(
            None,
            remote_snap_pre_merge.partial_cmp(&snap_b_neighborhood)
        );
        assert!(!(snap_b_neighborhood < remote_snap_pre_merge));
        assert_eq!(remote_snap_pre_merge.tracer_id, remote_tracer_id);
        assert_eq!(1, remote_snap_pre_merge.buckets_len);

        tracer_merge_history(remote_tracer, &snap_b_neighborhood as *const CausalSnapshot);

        let remote_snap_post_merge = tracer_snapshot(remote_tracer);
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

        let snap_c = tracer_snapshot(tracer);
        assert!(snap_b < snap_c);
        assert!(!(snap_c < snap_b));
    }

    #[test]
    fn confirm_tracer_size() {
        assert_eq!(32, core::mem::size_of::<Tracer<'static, 'static>>());
    }
}
// TODO - static assertions?
// TODO - should we expose comparison operations for CausalSnapshot?
// TODO - make tracer size dynamic - both tunable and fit to available space
