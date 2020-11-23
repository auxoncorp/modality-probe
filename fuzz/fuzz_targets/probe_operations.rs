#![no_main]
use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

use core::mem::MaybeUninit;
use modality_probe::*;

#[derive(Arbitrary, Debug)]
struct Script {
    buffer_size: u16,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    RecordTime(u64),
    RecordEvent(u32),
    RecordEventWithTime(u32, u64),
    RecordEventWithPayload(u32, u32),
    RecordEventWithPayloadWithTime(u32, u32, u64),
    ProduceSnapshot,
    ProduceSnapshotWithTime(u64),
    MergeSnapshot(ArbSnapshot),
    MergeSnapshotWithTime(ArbSnapshot, u64),
    MergeSnapshotBytes([u8; 12]),
    MergeSnapshotBytesWithTime([u8; 12], u64),
    Report(u16),
}

#[derive(Arbitrary, Debug)]
struct ArbSnapshot {
    pub clock: ArbLogicalClock,
    pub reserved_0: [u8; 2],
    pub reserved_1: [u8; 2],
}

#[derive(Arbitrary, Debug)]
struct ArbLogicalClock {
    pub probe_id: u32,
    pub epoch: u16,
    pub ticks: u16,
}

fn run(s: Script) {
    if s.buffer_size > 1024 {
        return;
    }

    let mut storage = vec![MaybeUninit::new(0u8); s.buffer_size as usize];
    let probe = match ModalityProbe::try_initialize_at(
        &mut storage,
        1,
        NanosecondResolution::UNSPECIFIED,
        WallClockId::local_only(),
        RestartCounterProvider::NoRestartTracking,
    ) {
        Ok(p) => p,
        Err(_) => return,
    };

    for op in s.ops.into_iter() {
        match op {
            Op::RecordTime(ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    probe.record_time(ns);
                }
            }

            Op::RecordEvent(id) => {
                if let Some(id) = EventId::new(id) {
                    probe.record_event(id);
                }
            }

            Op::RecordEventWithTime(id, ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    if let Some(id) = EventId::new(id) {
                        probe.record_event_with_time(id, ns);
                    }
                }
            }

            Op::RecordEventWithPayload(id, payload) => {
                if let Some(id) = EventId::new(id) {
                    probe.record_event_with_payload(id, payload);
                }
            }

            Op::RecordEventWithPayloadWithTime(id, payload, ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    if let Some(id) = EventId::new(id) {
                        probe.record_event_with_payload_with_time(id, payload, ns);
                    }
                }
            }

            Op::ProduceSnapshot => {
                let _ = probe.produce_snapshot();
            }

            Op::ProduceSnapshotWithTime(ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    let _ss = probe.produce_snapshot_with_time(ns);
                }
            }

            Op::MergeSnapshot(ss) => {
                if let Some(id) = ProbeId::new(ss.clock.probe_id) {
                    let _ = probe.merge_snapshot(&CausalSnapshot {
                        clock: LogicalClock {
                            id,
                            epoch: ss.clock.epoch.into(),
                            ticks: ss.clock.ticks.into(),
                        },
                        reserved_0: ss.reserved_0,
                        reserved_1: ss.reserved_1,
                    });
                }
            }

            Op::MergeSnapshotWithTime(ss, ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    if let Some(id) = ProbeId::new(ss.clock.probe_id) {
                        let _ = probe.merge_snapshot_with_time(
                            &CausalSnapshot {
                                clock: LogicalClock {
                                    id,
                                    epoch: ss.clock.epoch.into(),
                                    ticks: ss.clock.ticks.into(),
                                },
                                reserved_0: ss.reserved_0,
                                reserved_1: ss.reserved_1,
                            },
                            ns,
                        );
                    }
                }
            }

            Op::MergeSnapshotBytes(bytes) => {
                let _ = probe.merge_snapshot_bytes(&bytes);
            }

            Op::MergeSnapshotBytesWithTime(bytes, ns) => {
                if let Some(ns) = Nanoseconds::new(ns) {
                    let _ = probe.merge_snapshot_bytes_with_time(&bytes, ns);
                }
            }

            Op::Report(dest_buffer_size) => {
                let mut dest_buffer = vec![0u8; dest_buffer_size as usize];
                let _ = probe.report(&mut dest_buffer);
            }
        }
    }
}

fuzz_target!(|s: Script| {
    run(s);
});
