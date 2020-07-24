use std::convert::TryFrom;
use std::mem;

use modality_probe::{
    log::LogEntry,
    wire::{
        le_bytes,
        report::{WireReport, WireReportError},
    },
    EventId, LogicalClock, ProbeId,
};

//TODO(dan@auxon.io): derive error.
#[derive(Debug)]
pub struct SerializationError;

impl From<WireReportError> for SerializationError {
    fn from(_: WireReportError) -> Self {
        SerializationError
    }
}

#[derive(Debug, PartialEq)]
pub struct Report {
    pub probe_id: ProbeId,
    pub probe_clock: LogicalClock,
    pub seq_num: u16,
    pub frontier_clocks: Vec<LogicalClock>,
    pub event_log: Vec<Event>,
}

#[derive(Debug, PartialEq)]
pub enum Event {
    Event(EventId),
    EventWithPayload(EventId, u32),
    TraceClock(LogicalClock),
}

impl TryFrom<&[u8]> for Report {
    type Error = SerializationError;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let report = WireReport::new(buf)?;
        let (epoch, ticks) = modality_probe::unpack_clock_word(report.clock());
        let id = report.probe_id()?;
        let mut owned_report = Report {
            probe_id: id,
            probe_clock: LogicalClock { id, epoch, ticks },
            seq_num: report.seq_num(),
            frontier_clocks: vec![],
            event_log: vec![],
        };

        let clocks_len = report.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let mut probe_id = None;
        let payload = report.payload();
        for u32_bytes in payload[..clocks_len].chunks_exact(mem::size_of::<LogEntry>()) {
            let raw = le_bytes::read_u32(u32_bytes);
            if probe_id.is_none() {
                probe_id = ProbeId::new(
                    unsafe { LogEntry::new_unchecked(raw) }.interpret_as_logical_clock_probe_id(),
                );
            } else {
                let (epoch, ticks) = modality_probe::unpack_clock_word(raw);
                owned_report.frontier_clocks.push(LogicalClock {
                    id: probe_id.expect("checked above that probe id is not none"),
                    epoch,
                    ticks,
                });
                probe_id = None;
            }
        }

        let mut interpret_next_as = Next::DontKnow;
        for u32_bytes in payload[clocks_len..].chunks_exact(mem::size_of::<LogEntry>()) {
            let raw = le_bytes::read_u32(u32_bytes);
            match interpret_next_as {
                Next::DontKnow => {
                    let raw_entry = unsafe { LogEntry::new_unchecked(raw) };
                    if raw_entry.has_clock_bit_set() {
                        interpret_next_as = Next::Clock(
                            ProbeId::new(raw_entry.interpret_as_logical_clock_probe_id())
                                .ok_or_else(|| SerializationError)?,
                        );
                    } else if raw_entry.has_event_with_payload_bit_set() {
                        interpret_next_as = Next::Payload(
                            raw_entry
                                .interpret_as_event_id()
                                .ok_or_else(|| SerializationError)?,
                        );
                    } else {
                        owned_report.event_log.push(Event::Event(
                            raw_entry
                                .interpret_as_event_id()
                                .ok_or_else(|| SerializationError)?,
                        ));
                    }
                }
                Next::Clock(id) => {
                    let (epoch, ticks) = modality_probe::unpack_clock_word(raw);
                    owned_report.event_log.push(Event::TraceClock(LogicalClock {
                        id,
                        epoch,
                        ticks,
                    }));
                    interpret_next_as = Next::DontKnow;
                }
                Next::Payload(id) => {
                    owned_report
                        .event_log
                        .push(Event::EventWithPayload(id, raw));
                    interpret_next_as = Next::DontKnow;
                }
            }
        }
        Ok(owned_report)
    }
}

enum Next {
    Clock(ProbeId),
    Payload(EventId),
    DontKnow,
}

#[cfg(test)]
mod test {
    use std::convert::TryFrom;

    use modality_probe::*;

    use super::*;
    #[test]
    fn report_e2e() {
        let mut storage1 = vec![0; 1024];
        let mut p1 = modality_probe::ModalityProbe::new_with_storage(
            &mut storage1,
            ProbeId::new(1).unwrap(),
        )
        .unwrap();

        let mut storage2 = vec![0; 1024];
        let mut p2 = modality_probe::ModalityProbe::new_with_storage(
            &mut storage2,
            ProbeId::new(2).unwrap(),
        )
        .unwrap();

        p1.record_event(EventId::new(1).unwrap());
        let mut report1 = vec![0; 512];
        let n_bytes = p1.report(&mut report1).unwrap();
        let mut o_report = Report::try_from(&report1[..n_bytes]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(1).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                seq_num: 0,
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![Event::Event(EventId::new(1).unwrap())],
            }
        );

        let snap = p1.produce_snapshot().unwrap();
        p2.record_event(EventId::new(2).unwrap());
        p2.merge_snapshot(&snap).unwrap();
        let n_bytes = p1.report(&mut report1).unwrap();
        o_report = Report::try_from(&report1[..n_bytes]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(1).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                seq_num: 0,
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![Event::TraceClock(LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                })],
            }
        );
        let n_bytes = p2.report(&mut report1).unwrap();
        o_report = Report::try_from(&report1[..n_bytes]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(2).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                seq_num: 0,
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    Event::Event(EventId::new(2).unwrap()),
                    Event::TraceClock(LogicalClock {
                        id: ProbeId::new(2).unwrap(),
                        epoch: ProbeEpoch(1),
                        ticks: ProbeTicks(1),
                    }),
                    Event::TraceClock(LogicalClock {
                        id: ProbeId::new(1).unwrap(),
                        epoch: ProbeEpoch(0),
                        ticks: ProbeTicks(0),
                    })
                ],
            }
        );
    }
}
