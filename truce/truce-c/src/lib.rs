#![no_std]
#![feature(lang_items, core_intrinsics)]
use truce::*;
pub use truce::{CausalSnapshot, Tracer};

#[no_mangle]
pub extern "C" fn tracer_initialize(
    destination: *mut u8,
    destination_size_bytes: usize,
    tracer_id: u32,
) -> *mut Tracer<'static> {
    assert!(
        !destination.is_null(),
        "tracer destination pointer was null"
    );
    assert!(
        destination_size_bytes >= core::mem::size_of::<Tracer<'static>>(),
        "insufficient tracer destination bytes to store the tracer"
    );
    unsafe {
        Tracer::initialize_at(
            core::slice::from_raw_parts_mut(destination, destination_size_bytes),
            TracerId::new(tracer_id).expect("tracer_id was zero or over the max allowed value"),
        )
        .expect("Could not initialize Tracer")
    }
}

#[no_mangle]
pub extern "C" fn tracer_record_event(tracer: *mut Tracer<'static>, event_id: u32) {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .record_event(EventId::new(event_id).expect("Could not create a non-zero EventId"))
}

#[no_mangle]
pub extern "C" fn tracer_write_log_report(
    tracer: *mut Tracer<'static>,
    log_report_destination: *mut u8,
    log_report_destination_size_bytes: usize,
) -> usize {
    assert!(
        !log_report_destination.is_null(),
        "log report destination pointer was null"
    );
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .write_log_report(unsafe {
            core::slice::from_raw_parts_mut(
                log_report_destination,
                log_report_destination_size_bytes,
            )
        })
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn tracer_share_history(
    tracer: *mut Tracer<'static>,
    history_destination: *mut u8,
    history_destination_bytes: usize,
) -> usize {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .share_history(unsafe {
            core::slice::from_raw_parts_mut(history_destination, history_destination_bytes)
        })
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn tracer_share_fixed_size_history(
    tracer: *mut Tracer<'static>,
    destination_snapshot: *mut CausalSnapshot,
) -> bool {
    unsafe {
        let tracer = tracer.as_mut().expect("tracer pointer was null");
        *destination_snapshot = match tracer.share_fixed_size_history() {
            Ok(snapshot) => snapshot,
            Err(_) => return false,
        };
        true
    }
}

#[no_mangle]
pub extern "C" fn tracer_merge_history(
    tracer: *mut Tracer<'static>,
    history_source: *const u8,
    history_source_bytes: usize,
) -> i32 {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .merge_history(unsafe { core::slice::from_raw_parts(history_source, history_source_bytes) })
        .is_ok()
        .as_i32_bool()
}

#[no_mangle]
pub extern "C" fn tracer_merge_fixed_size_history(
    tracer: *mut Tracer<'static>,
    snapshot: *const CausalSnapshot,
) -> i32 {
    unsafe { tracer.as_mut() }
        .expect("tracer pointer was null")
        .merge_fixed_size_history(unsafe { &*snapshot })
        .is_ok()
        .as_i32_bool()
}

trait AsInt32Bool {
    fn as_i32_bool(self) -> i32;
}

impl AsInt32Bool for bool {
    fn as_i32_bool(self) -> i32 {
        if self {
            1
        } else {
            0
        }
    }
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
    use core::mem::MaybeUninit;

    fn stack_snapshot(tracer: *mut Tracer<'static>) -> CausalSnapshot {
        let mut snap = MaybeUninit::uninit();
        assert!(tracer_share_fixed_size_history(tracer, snap.as_mut_ptr()));
        unsafe { snap.assume_init() }
    }

    #[test]
    fn end_to_end_use_of_tracer_capi_works() {
        let mut backend = [0u8; 2099];

        let tracer_id = 2;
        let mut storage = [0u8; 1024];
        let storage_slice = &mut storage;
        let tracer = tracer_initialize(
            storage_slice.as_mut_ptr() as *mut u8,
            storage_slice.len(),
            tracer_id,
        );
        let snap_empty = stack_snapshot(tracer);
        assert_eq!(snap_empty.tracer_id, tracer_id);
        assert_eq!(1, snap_empty.buckets_len);
        tracer_record_event(tracer, 100);
        let snap_a = stack_snapshot(tracer);
        assert!(snap_empty < snap_a);
        assert!(!(snap_a < snap_empty));
        assert_eq!(1, snap_a.buckets_len);

        assert!(&backend.iter().all(|b| *b == 0));
        let bytes_written = tracer_write_log_report(tracer, backend.as_mut_ptr(), backend.len());
        assert!(bytes_written > 0);
        assert!(!&backend.iter().all(|b| *b == 0));
        let snap_b = stack_snapshot(tracer);
        // We expect the local clock to have progressed thanks to recording an event
        // internally when we successfully transmitted the state to the backend.
        assert!(snap_a < snap_b);
        assert!(!(snap_b < snap_a));
        let snap_b_neighborhood = stack_snapshot(tracer);
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
        );
        let remote_snap_pre_merge = stack_snapshot(remote_tracer);
        // Since we haven't manually combined history information yet, the remote's history is disjoint
        assert_eq!(
            None,
            remote_snap_pre_merge.partial_cmp(&snap_b_neighborhood)
        );
        assert!(!(snap_b_neighborhood < remote_snap_pre_merge));
        assert_eq!(remote_snap_pre_merge.tracer_id, remote_tracer_id);
        assert_eq!(1, remote_snap_pre_merge.buckets_len);

        tracer_merge_fixed_size_history(
            remote_tracer,
            &snap_b_neighborhood as *const CausalSnapshot,
        );

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
