use std::{
    convert::TryFrom,
    io::{Read, Write},
    iter::Peekable,
};

use modality_probe::{EventId, LogicalClock, ProbeEpoch, ProbeId, ProbeTicks};

use super::{
    EventLogEntry, LogFileRow, ReadError, Report, ReportLogEntry, SequenceNumber, SessionId,
};

pub fn write_log_entries<'a, W: Write, E: IntoIterator<Item = &'a ReportLogEntry>>(
    w: &mut W,
    entries: E,
    include_header_row: bool,
) -> Result<(), csv::Error> {
    let mut csv = csv::WriterBuilder::new()
        .has_headers(include_header_row)
        .from_writer(w);

    for e in entries.into_iter() {
        let line: LogFileRow = e.into();
        csv.serialize(line)?;
    }

    csv.flush()?;
    Ok(())
}

impl From<csv::Error> for ReadError {
    fn from(e: csv::Error) -> ReadError {
        ReadError::Serialization(format!("csv failure: {}", e))
    }
}

impl From<&csv::Error> for ReadError {
    fn from(e: &csv::Error) -> ReadError {
        ReadError::Serialization(format!("csv failure: {}", e))
    }
}

pub fn read_log_entries<R: Read>(r: &mut R) -> Result<Vec<ReportLogEntry>, ReadError> {
    let mut csv = csv::Reader::from_reader(r);
    csv.deserialize()
        .map(|line| Ok(ReportLogEntry::try_from(&line?)?))
        .collect()
}

// TODO(dan@auxon.io): MOVE ME; GENERALIZE ERROR TYPE
pub struct CsvReportIter<I>
where
    I: Iterator<Item = Result<LogFileRow, csv::Error>>,
{
    // If this iterator encounters an error while accumulating a
    // report, it stops in place, rendering it unusable. By storing
    // that error, we can keep the iterator from being used again.
    // TODO(dan@auxon.io): new-ify these
    pub error: Option<ReadError>,
    pub report_items: Peekable<I>,
}

impl<I> Iterator for CsvReportIter<I>
where
    I: Iterator<Item = Result<LogFileRow, csv::Error>>,
{
    type Item = Result<Report, ReadError>;
    fn next(&mut self) -> Option<Result<Report, ReadError>> {
        if self.error.is_some() {
            return self.error.clone().map(Err);
        }

        let next = match self.report_items.peek() {
            Some(Ok(e)) => e,
            Some(Err(e)) => return Some(Err(e.into())),
            None => return None,
        };
        let probe_id = match ProbeId::new(next.probe_id) {
            Some(id) => id,
            None => {
                self.error = Some(ReadError::InvalidContent {
                    session_id: SessionId(next.session_id),
                    sequence_number: SequenceNumber(next.sequence_number),
                    sequence_index: next.sequence_index,
                    message: "invalid probe id",
                });
                return self.error.clone().map(Err);
            }
        };

        let seq_num = next.sequence_number;
        let mut report = Report {
            probe_id,
            probe_clock: LogicalClock {
                id: probe_id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
            seq_num: SequenceNumber(next.sequence_number),
            frontier_clocks: Vec::new(),
            event_log: Vec::new(),
        };

        loop {
            let next = match self.report_items.peek() {
                Some(Ok(e)) => e,
                Some(Err(e)) => return Some(Err(e.into())),
                None => return Some(Ok(report)),
            };
            if next.probe_id != probe_id.get_raw() || next.sequence_number != seq_num {
                return Some(Ok(report));
            }

            // we peeked at this item above.
            let e = self.report_items.next().unwrap().unwrap();
            if e.is_frontier_clock() {
                let id = match ProbeId::new(e.probe_id) {
                    Some(id) => id,
                    None => {
                        self.error = Some(ReadError::InvalidContent {
                            session_id: SessionId(e.session_id),
                            sequence_number: SequenceNumber(e.sequence_number),
                            sequence_index: e.sequence_index,
                            message: "invalid probe id",
                        });
                        return self.error.clone().map(Err);
                    }
                };
                let epoch = ProbeEpoch(e.fc_probe_epoch.expect("already checked fc epoch"));
                let ticks = ProbeTicks(e.fc_probe_clock.expect("already checked fc clock"));
                if id == report.probe_id {
                    report.probe_clock = LogicalClock { id, epoch, ticks };
                }
                report
                    .frontier_clocks
                    .push(LogicalClock { id, epoch, ticks });
            } else if e.is_trace_clock() {
                let id = match ProbeId::new(e.tc_probe_id.expect("already checked tc probe id")) {
                    Some(id) => id,
                    None => {
                        self.error = Some(ReadError::InvalidContent {
                            session_id: SessionId(e.session_id),
                            sequence_number: SequenceNumber(e.sequence_number),
                            sequence_index: e.sequence_index,
                            message: "invalid probe id",
                        });
                        return self.error.clone().map(Err);
                    }
                };
                let epoch = ProbeEpoch(e.tc_probe_epoch.expect("already checked fc epoch"));
                let ticks = ProbeTicks(e.tc_probe_clock.expect("already checked fc clock"));
                report
                    .event_log
                    .push(EventLogEntry::TraceClock(LogicalClock { id, epoch, ticks }));
                if id == report.probe_id {
                    report.probe_clock = LogicalClock { id, epoch, ticks };
                }
            } else {
                if let Some(eid) = e.event_id {
                    let id = match EventId::new(eid) {
                        Some(id) => id,
                        None => {
                            self.error = Some(ReadError::InvalidContent {
                                session_id: SessionId(e.session_id),
                                sequence_number: SequenceNumber(e.sequence_number),
                                sequence_index: e.sequence_index,
                                message: "invalid event id",
                            });
                            return self.error.clone().map(Err);
                        }
                    };
                    report
                        .event_log
                        .push(if let Some(payload) = e.event_payload {
                            EventLogEntry::EventWithPayload(id, payload)
                        } else {
                            EventLogEntry::Event(id)
                        });
                } else {
                    return Some(Err(ReadError::InvalidContent {
                        session_id: SessionId(e.session_id),
                        sequence_number: SequenceNumber(e.sequence_number),
                        sequence_index: e.sequence_index,
                        message: "missing an event id",
                    }));
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn round_trip_serialization(
            entries in proptest::collection::vec(
                crate::test::arb_log_entry(),
                0..15
            )
        ) {
            let mut data = Vec::<u8>::new();
            prop_assert!(super::write_log_entries(&mut data, &entries, true).is_ok());

            let read_back = super::read_log_entries(&mut data.as_slice());

            match read_back {
                Err(e) => prop_assert!(false, "read_back error: {:?}", e),
                Ok(es) => prop_assert_eq!(entries, es),
            }
        }
    }
}
