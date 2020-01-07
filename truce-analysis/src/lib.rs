use chrono::prelude::*;
use serde;
use std::convert::TryFrom;
use std::io::{Read, Write};

mod model;

#[derive(Debug, serde::Serialize, serde::Deserialize, Eq, PartialEq)]
struct LogFileLine {
    id: u32,
    receive_time: DateTime<Utc>,
    tracer_id: u32,
    event_id: Option<u32>,
    lc_tracer_id: Option<u32>,
    lc_clock: Option<u32>,
    preceding_entry: Option<u32>,
}

impl From<&model::LogEntry> for LogFileLine {
    fn from(e: &model::LogEntry) -> LogFileLine {
        LogFileLine {
            id: e.id.0,
            tracer_id: e.tracer_id.0,
            event_id: match &e.data {
                model::LogEntryData::Event(id) => Some(id.0),
                _ => None,
            },
            lc_tracer_id: match &e.data {
                model::LogEntryData::LogicalClock(tracer_id, _) => Some(tracer_id.0),
                _ => None,
            },
            lc_clock: match &e.data {
                model::LogEntryData::LogicalClock(_, clock) => Some(*clock),
                _ => None,
            },
            preceding_entry: match &e.preceding_entry {
                Some(id) => Some(id.0),
                None => None,
            },
            receive_time: e.receive_time,
        }
    }
}

#[derive(Debug)]
pub enum ReadError {
    InvalidContent {
        log_entry_id: model::LogEntryId,
        message: &'static str,
    },
    Csv(csv::Error),
}

impl From<csv::Error> for ReadError {
    fn from(e: csv::Error) -> ReadError {
        ReadError::Csv(e)
    }
}

impl TryFrom<&LogFileLine> for model::LogEntry {
    type Error = ReadError;

    fn try_from(l: &LogFileLine) -> Result<model::LogEntry, Self::Error> {
        let log_entry_id: model::LogEntryId = l.id.into();

        let data = if let Some(event_id) = l.event_id {
            if l.lc_tracer_id.is_some() {
                return Err(ReadError::InvalidContent {
                    log_entry_id,
                    message: "When event_id is present, lc_tracer_id must be empty",
                });
            } else if l.lc_clock.is_some() {
                return Err(ReadError::InvalidContent {
                    log_entry_id,
                    message: "When event_id is present, lc_clock must be empty",
                });
            }

            model::LogEntryData::Event(model::EventId(event_id))
        } else if let Some(lc_tracer_id) = l.lc_tracer_id {
            match l.lc_clock {
                None => {
                    return Err(ReadError::InvalidContent {
                        log_entry_id,
                        message: "When lc_tracer_id is present, lc_clock must also be present",
                    });
                }
                Some(lc_clock) => model::LogEntryData::LogicalClock(lc_tracer_id.into(), lc_clock),
            }
        } else {
            return Err(ReadError::InvalidContent {
                log_entry_id,
                message: "Either event_id must be present, or both lc_tracer_id and lc_clock must both be present",
            });
        };

        Ok(model::LogEntry {
            id: log_entry_id,
            tracer_id: l.tracer_id.into(),
            data,
            preceding_entry: l.preceding_entry.map(|id| id.into()),
            receive_time: l.receive_time,
        })
    }
}

pub fn write_csv_log_entries<'a, W: Write, E: IntoIterator<Item = &'a model::LogEntry>>(
    w: &mut W,
    entries: E,
    include_header_row: bool,
) -> Result<(), csv::Error> {
    let mut csv = csv::WriterBuilder::new()
        .has_headers(include_header_row)
        .from_writer(w);

    for e in entries.into_iter() {
        let line: LogFileLine = e.into();
        csv.serialize(line)?;
    }

    csv.flush()?;
    Ok(())
}

pub fn read_csv_log_entries<'a, R: Read>(r: &mut R) -> Result<Vec<model::LogEntry>, ReadError> {
    let mut csv = csv::Reader::from_reader(r);
    csv.deserialize()
        .map(|line| Ok(model::LogEntry::try_from(&line?)?))
        .collect()
}

#[cfg(test)]
mod test {
    //use super::model::*;
    use super::*;
    //use chrono::prelude::*;
    use proptest::prelude::*;

    fn arb_log_file_line() -> impl Strategy<Value = LogFileLine> {
        (
            any::<u32>(),
            model::test::arb_datetime(),
            any::<u32>(),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
        )
            .prop_map(
                |(
                    id,
                    receive_time,
                    tracer_id,
                    event_id,
                    lc_tracer_id,
                    lc_clock,
                    preceding_entry,
                )| LogFileLine {
                    id,
                    receive_time,
                    tracer_id,
                    event_id,
                    lc_tracer_id,
                    lc_clock,
                    preceding_entry,
                },
            )
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 1000, .. ProptestConfig::default()})]

        #[test]
        fn entry_to_line_round_trip(entry in model::test::arb_log_entry())
        {
            let line : LogFileLine = (&entry).into();
            match model::LogEntry::try_from(&line) {
                Err(err) => prop_assert!(false, "convert back error: {:?}", err),
                Ok(e2) => prop_assert_eq!(entry, e2),
            }
        }


        #[test]
        fn line_to_entry_round_trip(line in arb_log_file_line())
        {
            match model::LogEntry::try_from(&line) {
                // This should fail sometimes, but always in the same way
                Err(ReadError::InvalidContent{ log_entry_id, .. }) =>
                    prop_assert_eq!(log_entry_id.0, line.id),

                Err(err) =>
                    prop_assert!(false, "Unexpected conversion error: {:?}", err),

                Ok(entry) => {
                    let l2: LogFileLine = (&entry).into();
                    prop_assert_eq!(line, l2);
                },
            }
        }

        #[test]
        fn round_trip_serialization(
            entries in proptest::collection::vec(model::test::arb_log_entry(),
                                                 0..15))
        {
            let mut data = Vec::<u8>::new();
            prop_assert!(write_csv_log_entries(&mut data, &entries, true).is_ok());

            let read_back = read_csv_log_entries(&mut data.as_slice());

            match read_back {
                Err(e) => prop_assert!(false, "read_back error: {:?}", e),
                Ok(es) => prop_assert_eq!(entries, es),
            }
        }
    }
}
