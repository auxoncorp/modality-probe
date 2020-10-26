#![deny(warnings)]

use core::{mem::MaybeUninit, ptr};
use modality_probe::{wire::WireReport, LogicalClock, ProbeId};
use modality_probe_capi_impl::*;
use proptest::prelude::*;

#[test]
fn initialization_errors() {
    let probe_id = 1;

    {
        let mut probe = MaybeUninit::uninit();
        let err = unsafe {
            modality_probe_initialize(
                ptr::null_mut(), // NULL storage pointer
                1024,
                probe_id,
                0,
                0,
                None,
                ptr::null_mut(),
                probe.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);
    }

    {
        let mut probe = MaybeUninit::uninit();
        let mut storage = [MaybeUninit::new(0u8); 512];
        let err = unsafe {
            modality_probe_initialize(
                storage.as_mut_ptr(),
                0, // Zero storage size
                probe_id,
                0,
                0,
                None,
                ptr::null_mut(),
                probe.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES, err);
    }

    {
        let mut storage = [MaybeUninit::new(0u8); 512];
        let err = unsafe {
            modality_probe_initialize(
                storage.as_mut_ptr(),
                storage.len(),
                probe_id,
                0,
                0,
                None,
                ptr::null_mut(),
                ptr::null_mut(), // NULL probe pointer
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);
    }
}

#[test]
fn event_recording_errors() {
    let err = unsafe { modality_probe_record_event(ptr::null_mut(), 100) };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe { modality_probe_record_event_with_payload(ptr::null_mut(), 100, 123) };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let probe_id = 1;
    let mut probe = MaybeUninit::uninit();
    let mut storage = [MaybeUninit::new(0u8); 512];
    let err = unsafe {
        modality_probe_initialize(
            storage.as_mut_ptr(),
            storage.len(),
            probe_id,
            0,
            0,
            None,
            ptr::null_mut(),
            probe.as_mut_ptr(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_OK, err);
    let probe = unsafe { probe.assume_init() };

    let err = unsafe { modality_probe_record_event(probe, 0) };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_EVENT_ID, err);

    let err = unsafe { modality_probe_record_event_with_payload(probe, 0, 0) };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_EVENT_ID, err);

    let err = unsafe { modality_probe_record_time(probe, core::u64::MAX) };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);

    let err = unsafe { modality_probe_record_event_with_time(probe, 1, core::u64::MAX) };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);

    let err =
        unsafe { modality_probe_record_event_with_payload_with_time(probe, 1, 2, core::u64::MAX) };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);
}

#[test]
fn reporting_errors() {
    let mut report_buffer = [0u8; 1024];

    {
        let mut bytes_written: usize = 0;
        let err = unsafe {
            modality_probe_report(
                ptr::null_mut(), // NULL probe pointer
                report_buffer.as_mut_ptr(),
                report_buffer.len(),
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);
        assert_eq!(bytes_written, 0);
    }

    let probe_id = 1;
    let mut probe = MaybeUninit::uninit();
    let mut storage = [MaybeUninit::new(0u8); 512];
    let err = unsafe {
        modality_probe_initialize(
            storage.as_mut_ptr(),
            storage.len(),
            probe_id,
            0,
            0,
            None,
            ptr::null_mut(),
            probe.as_mut_ptr(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_OK, err);
    let probe = unsafe { probe.assume_init() };

    {
        let mut bytes_written: usize = 0;
        let err = unsafe {
            modality_probe_report(
                probe,
                ptr::null_mut(), // NULL buffer pointer
                report_buffer.len(),
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);
        assert_eq!(bytes_written, 0);
    }

    {
        let mut bytes_written: usize = 0;
        let err = unsafe {
            modality_probe_report(
                probe,
                report_buffer.as_mut_ptr(),
                0, // Zero buffer size
                &mut bytes_written as *mut usize,
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES, err);
        assert_eq!(bytes_written, 0);
    }

    {
        let err = unsafe {
            modality_probe_report(
                probe,
                report_buffer.as_mut_ptr(),
                report_buffer.len(),
                ptr::null_mut(), // NULL bytes_written pointer
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);
    }
}

#[test]
fn produce_snapshot_errors() {
    let mut bytes_written: usize = 0;
    let mut snapshot_bytes = [0_u8; 12];
    let mut snapshot = CausalSnapshot {
        clock: LogicalClock {
            id: ProbeId::new(1).unwrap(),
            epoch: 0.into(),
            ticks: 0.into(),
        },
        reserved_0: [0, 0],
        reserved_1: [0, 0],
    };

    let err = unsafe {
        modality_probe_produce_snapshot(
            ptr::null_mut(), // NULL probe pointer
            &mut snapshot as *mut _,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_produce_snapshot_bytes(
            ptr::null_mut(), // NULL probe pointer
            snapshot_bytes.as_mut_ptr(),
            snapshot_bytes.len(),
            &mut bytes_written as *mut usize,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let probe_id = 1;
    let mut probe = MaybeUninit::uninit();
    let mut storage = [MaybeUninit::new(0u8); 512];
    let err = unsafe {
        modality_probe_initialize(
            storage.as_mut_ptr(),
            storage.len(),
            probe_id,
            0,
            0,
            None,
            ptr::null_mut(),
            probe.as_mut_ptr(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_OK, err);
    let probe = unsafe { probe.assume_init() };

    let err = unsafe {
        modality_probe_produce_snapshot(
            probe,
            ptr::null_mut(), // NULL snapshot pointer
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_produce_snapshot_with_time(
            probe,
            core::u64::MAX, // Invalid time
            &mut snapshot as *mut _,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);

    let err = unsafe {
        modality_probe_produce_snapshot_bytes(
            probe,
            ptr::null_mut(), // NULL snapshot pointer
            snapshot_bytes.len(),
            &mut bytes_written as *mut usize,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_produce_snapshot_bytes(
            probe,
            snapshot_bytes.as_mut_ptr(),
            0, // Zero size
            &mut bytes_written as *mut usize,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES, err);

    let err = unsafe {
        modality_probe_produce_snapshot_bytes(
            probe,
            snapshot_bytes.as_mut_ptr(),
            snapshot_bytes.len(),
            ptr::null_mut(), // NULL bytes_written
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_produce_snapshot_bytes_with_time(
            probe,
            core::u64::MAX, // Invalid time
            snapshot_bytes.as_mut_ptr(),
            snapshot_bytes.len(),
            &mut bytes_written as *mut usize,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);
}

#[test]
fn merge_snapshot_errors() {
    let snapshot_bytes = [0_u8; 12];
    let snapshot = CausalSnapshot {
        clock: LogicalClock {
            id: ProbeId::new(1).unwrap(),
            epoch: 0.into(),
            ticks: 0.into(),
        },
        reserved_0: [0, 0],
        reserved_1: [0, 0],
    };

    let err = unsafe {
        modality_probe_merge_snapshot(
            ptr::null_mut(), // NULL probe pointer
            &snapshot as *const _,
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_merge_snapshot_bytes(
            ptr::null_mut(), // NULL probe pointer
            snapshot_bytes.as_ptr(),
            snapshot_bytes.len(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let probe_id = 1;
    let mut probe = MaybeUninit::uninit();
    let mut storage = [MaybeUninit::new(0u8); 512];
    let err = unsafe {
        modality_probe_initialize(
            storage.as_mut_ptr(),
            storage.len(),
            probe_id,
            0,
            0,
            None,
            ptr::null_mut(),
            probe.as_mut_ptr(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_OK, err);
    let probe = unsafe { probe.assume_init() };

    let err = unsafe {
        modality_probe_merge_snapshot(
            probe,
            ptr::null(), // NULL snapshot pointer
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_merge_snapshot_with_time(
            probe,
            &snapshot as *const _,
            core::u64::MAX, // Invalid time
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);

    let err = unsafe {
        modality_probe_merge_snapshot_bytes(
            probe,
            ptr::null(), // NULL snapshot pointer
            snapshot_bytes.len(),
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_NULL_POINTER, err);

    let err = unsafe {
        modality_probe_merge_snapshot_bytes(
            probe,
            snapshot_bytes.as_ptr(),
            0, // Zero size
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_SOURCE_BYTES, err);

    let err = unsafe {
        modality_probe_merge_snapshot_bytes_with_time(
            probe,
            snapshot_bytes.as_ptr(),
            snapshot_bytes.len(),
            core::u64::MAX, // Invalid time
        )
    };
    assert_eq!(MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME, err);
}

#[test]
fn now_errors() {
    let now = unsafe { modality_probe_now(ptr::null_mut()) };
    assert_eq!(now.clock.id.get_raw(), 0);
    assert_eq!(now.clock.epoch.0, 0);
    assert_eq!(now.clock.ticks.0, 0);
    assert_eq!(now.event_count, 0);
}

proptest! {
    #[test]
    fn probe_reporting(
        report_buffer_capacity in 0_usize..256_usize,
        num_events in 0_usize..256_usize,
        num_events_with_payload in 0_usize..256_usize,
        event_payload in proptest::num::u32::ANY,
    ) {
        let mut report_buffer_storage = [0u8; 1024];
        let report_buffer = &mut report_buffer_storage[..report_buffer_capacity];
        prop_assert!(report_buffer.len() <= report_buffer.len());

        let probe_id = 1;
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let storage_slice = &mut storage;
        let mut probe = MaybeUninit::uninit();
        let err = unsafe {
            modality_probe_initialize(
                storage_slice.as_mut_ptr(),
                storage_slice.len(),
                probe_id,
                0,
                0,
                None,
                ptr::null_mut(),
                probe.as_mut_ptr(),
            )
        };
        prop_assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        let probe = unsafe { probe.assume_init() };

        for _ in 0..num_events {
            let err = unsafe { modality_probe_record_event(probe, 100) };
            prop_assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        }

        for _ in 0..num_events_with_payload {
            let err = unsafe {
                modality_probe_record_event_with_payload(probe, 101, event_payload)
            };
            prop_assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        }

        let mut bytes_written: usize = 0;
        let err = unsafe {
            modality_probe_report(
                probe,
                report_buffer.as_mut_ptr(),
                report_buffer.len(),
                &mut bytes_written as *mut usize,
            )
        };

        if report_buffer_capacity < WireReport::<&[u8]>::buffer_len(0, 1) {
            prop_assert_eq!(bytes_written, 0);
            prop_assert_eq!(MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES, err);
        } else {
            prop_assert!(bytes_written > 0);
            prop_assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        }
    }
}

proptest! {
    #[test]
    fn snapshot_exchanges_advance_clock(num_snapshot_exchanges in 1_usize..=1024_usize) {
        let probe_id_foo = 1;
        let mut storage_foo = [MaybeUninit::new(0u8); 512];
        let mut probe_foo = MaybeUninit::uninit();
        let err = unsafe {
            modality_probe_initialize(
                storage_foo.as_mut_ptr(),
                storage_foo.len(),
                probe_id_foo,
                0,
                0,
                None,
                ptr::null_mut(),
                probe_foo.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        let probe_foo = unsafe { probe_foo.assume_init() };

        let probe_id_bar = 2;
        let mut storage_bar = [MaybeUninit::new(0u8); 512];
        let mut probe_bar = MaybeUninit::uninit();
        let err = unsafe {
            modality_probe_initialize(
                storage_bar.as_mut_ptr(),
                storage_bar.len(),
                probe_id_bar,
                0,
                0,
                None,
                ptr::null_mut(),
                probe_bar.as_mut_ptr(),
            )
        };
        assert_eq!(MODALITY_PROBE_ERROR_OK, err);
        let probe_bar = unsafe { probe_bar.assume_init() };

        let mut prev_now_foo = unsafe { modality_probe_now(probe_foo) };
        assert_eq!(prev_now_foo.clock.id.get_raw(), probe_id_foo);
        assert_ne!(prev_now_foo.event_count, 0);

        let mut prev_now_bar = unsafe { modality_probe_now(probe_bar) };
        assert_eq!(prev_now_bar.clock.id.get_raw(), probe_id_bar);
        assert_ne!(prev_now_bar.event_count, 0);

        for _ in 0..num_snapshot_exchanges {
            let mut snapshot_buffer = [0u8; 12];
            let mut bytes_written: usize = 0;

            let err = unsafe { modality_probe_record_event(probe_foo, 100) };
            assert_eq!(MODALITY_PROBE_ERROR_OK, err);

            let err = unsafe {
                modality_probe_produce_snapshot_bytes(
                    probe_foo,
                    snapshot_buffer.as_mut_ptr(),
                    snapshot_buffer.len(),
                    &mut bytes_written as *mut usize,
                )
            };
            assert_eq!(MODALITY_PROBE_ERROR_OK, err);
            assert!(bytes_written > 0);

            let err = unsafe {
                modality_probe_merge_snapshot_bytes(probe_bar, snapshot_buffer.as_ptr(), bytes_written)
            };
            assert_eq!(MODALITY_PROBE_ERROR_OK, err);

            let now_foo = unsafe { modality_probe_now(probe_foo) };
            assert_eq!(now_foo.clock.id.get_raw(), probe_id_foo);
            assert!(now_foo.clock > prev_now_foo.clock);

            let now_bar = unsafe { modality_probe_now(probe_bar) };
            assert_eq!(now_bar.clock.id.get_raw(), probe_id_bar);
            assert!(now_bar.clock > prev_now_bar.clock);

            prev_now_foo = now_foo;
            prev_now_bar = now_bar;
        }
    }
}
