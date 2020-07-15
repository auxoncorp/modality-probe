use std::convert::{TryFrom, TryInto};

use chrono::prelude::*;
use modality_probe::{
    compact_log::LogEvent, report::wire::LogReport, EventId, ProbeClock, ProbeEpoch, ProbeId,
};

pub mod csv;

macro_rules! newtype {
   ($(#[$meta:meta])* pub struct $name:ident(pub $t:ty);) => {
        $(#[$meta])*
        pub struct $name(pub $t);

        impl From<$t> for $name {
            fn from(val: $t) -> $name {
                $name(val)
            }
        }

        impl Into<$t> for &$name {
            fn into(self) -> $t {
                self.0
            }
        }
    };
}

newtype! {
    /// A logical event scope
    ///
    /// A session is an arbitrary scope for log events. Event ordering is (via
    /// sequence and logical clocks) is resolved between events in the same
    /// session.
    #[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
    pub struct SessionId(pub u32);
}

newtype! {
    /// A log segment
    ///
    /// The log is divided into segments, each of which begins with some logical
    /// clock entries and ends with a sequence of events. The id must be unique
    /// within the session.
    #[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
    pub struct SegmentId(pub u32);
}

/// Map an event id to its name and description
#[derive(Debug, Eq, PartialEq)]
pub struct EventMapping {
    id: EventId,
    name: String,
    description: String,
}

/// Map a probe id to its name and description
#[derive(Debug, Eq, PartialEq)]
pub struct ProbeMapping {
    id: ProbeId,
    name: String,
    description: String,
}

/// The data that may be attached to a log entry
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LogEntryData {
    Event(EventId),
    EventWithPayload(EventId, u32),
    LogicalClock(ProbeId, ProbeEpoch, ProbeClock),
}

impl From<EventId> for LogEntryData {
    fn from(val: EventId) -> LogEntryData {
        LogEntryData::Event(val)
    }
}

impl From<(ProbeId, ProbeEpoch, ProbeClock)> for LogEntryData {
    fn from((id, epoch, clock): (ProbeId, ProbeEpoch, ProbeClock)) -> LogEntryData {
        LogEntryData::LogicalClock(id, epoch, clock)
    }
}

#[derive(Debug)]
pub enum ReadError {
    InvalidContent {
        session_id: SessionId,
        segment_id: SegmentId,
        segment_index: u32,
        message: &'static str,
    },
    Serialization(Box<dyn std::error::Error>),
}

/// A single entry in the log
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct LogEntry {
    /// The session in which this entry was made. Used to qualify the id field.
    pub session_id: SessionId,

    /// The segment to which this entry belongs
    pub segment_id: SegmentId,

    /// Where this entry occurs within the segment
    pub segment_index: u32,

    /// The probe that supplied this entry
    pub probe_id: ProbeId,

    /// This entry's data; an event, or a logical clock snapshot
    pub data: LogEntryData,

    /// The time this entry was received by the collector
    ///
    /// This is the collector's system clock at the time the entry data was
    /// received, not when it was created. It is stored for convenience only;
    /// the logical clock should be used for ordering messages.
    pub receive_time: DateTime<Utc>,
}

impl LogEntry {
    pub fn is_event(&self) -> bool {
        match self.data {
            LogEntryData::Event(_) | LogEntryData::EventWithPayload(_, _) => true,
            LogEntryData::LogicalClock(_, _, _) => false,
        }
    }

    pub fn is_clock(&self) -> bool {
        match self.data {
            LogEntryData::Event(_) | LogEntryData::EventWithPayload(_, _) => false,
            LogEntryData::LogicalClock(_, _, _) => true,
        }
    }
}

/// A row in a collected trace.
#[derive(Debug, serde::Serialize, serde::Deserialize, Eq, PartialEq)]
struct LogFileRow {
    session_id: u32,
    segment_id: u32,
    segment_index: u32,
    receive_time: DateTime<Utc>,
    probe_id: u32,
    event_id: Option<u32>,
    event_payload: Option<u32>,
    lc_probe_id: Option<u32>,
    lc_probe_epoch: Option<u16>,
    lc_probe_clock: Option<u16>,
}

impl From<&LogEntry> for LogFileRow {
    fn from(e: &LogEntry) -> LogFileRow {
        LogFileRow {
            session_id: e.session_id.0,
            segment_id: e.segment_id.0,
            segment_index: e.segment_index,
            probe_id: e.probe_id.get_raw(),
            event_id: match &e.data {
                LogEntryData::Event(id) => Some(id.get_raw()),
                LogEntryData::EventWithPayload(id, _) => Some(id.get_raw()),
                _ => None,
            },
            event_payload: match &e.data {
                LogEntryData::EventWithPayload(_, payload) => Some(*payload),
                _ => None,
            },
            lc_probe_id: match &e.data {
                LogEntryData::LogicalClock(probe_id, _, _) => Some(probe_id.get_raw()),
                _ => None,
            },
            lc_probe_epoch: match &e.data {
                LogEntryData::LogicalClock(_, probe_epoch, _) => Some(*probe_epoch),
                _ => None,
            },
            lc_probe_clock: match &e.data {
                LogEntryData::LogicalClock(_, _, probe_clock) => Some(*probe_clock),
                _ => None,
            },
            receive_time: e.receive_time,
        }
    }
}

impl TryFrom<&LogFileRow> for LogEntry {
    type Error = ReadError;

    fn try_from(l: &LogFileRow) -> Result<LogEntry, Self::Error> {
        let session_id: SessionId = l.session_id.into();
        let segment_id: SegmentId = l.segment_id.into();
        let segment_index: u32 = l.segment_index;

        let data = if let Some(event_id) = l.event_id {
            if l.lc_probe_id.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When event_id is present, lc_probe_id must be empty",
                });
            } else if l.lc_probe_epoch.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When event_id is present, lc_probe_epoch must be empty",
                });
            } else if l.lc_probe_clock.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When event_id is present, lc_probe_clock must be empty",
                });
            }

            let event_id = event_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "Invalid event id",
                })?;
            if let Some(payload) = l.event_payload {
                LogEntryData::EventWithPayload(event_id, payload)
            } else {
                LogEntryData::Event(event_id)
            }
        } else if let Some(lc_probe_id) = l.lc_probe_id {
            match (l.lc_probe_clock, l.lc_probe_epoch) {
                (None, _) => {
                    return Err(ReadError::InvalidContent {
                        session_id,
                        segment_id,
                        segment_index,
                        message: "When lc_probe_id is present, lc_probe_clock must also be present",
                    });
                },
                (_, None) => {
                    return Err(ReadError::InvalidContent {
                        session_id,
                        segment_id,
                        segment_index,
                        message: "When lc_probe_id is present, lc_probe_epoch must also be present",
                    });
                },
                (Some(lc_probe_clock), Some(lc_probe_epoch)) => LogEntryData::LogicalClock(lc_probe_id.try_into().map_err(|_e|
                    ReadError::InvalidContent {
                        session_id,
                        segment_id,
                        segment_index,
                        message: "When lc_probe_id is present, it must be a valid modality_probe::ProbeId",
                    }
                )?, lc_probe_epoch, lc_probe_clock),
            }
        } else {
            return Err(ReadError::InvalidContent {
                session_id, segment_id, segment_index,
                message: "Either event_id must be present, or both lc_probe_id and lc_clock must both be present",
            });
        };

        Ok(LogEntry {
            session_id,
            segment_id,
            segment_index,
            probe_id: l
                .probe_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message:
                        "When lc_probe_id is present, it must be a valid modality_probe::ProbeId",
                })?,
            data,
            receive_time: l.receive_time,
        })
    }
}

pub fn add_log_report_to_entries(
    log_report: &LogReport,
    session_id: SessionId,
    initial_segment_id: SegmentId,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<LogEntry>,
) -> u32 {
    let mut next_segment_id = initial_segment_id.0;
    let probe_id = log_report.probe_id;
    for segment in &log_report.segments {
        let mut segment_index = 0;

        for clock_bucket in &segment.clocks {
            log_entries_buffer.push(LogEntry {
                session_id,
                segment_id: next_segment_id.into(),
                segment_index,
                probe_id,
                data: LogEntryData::LogicalClock(
                    clock_bucket.id,
                    clock_bucket.epoch,
                    clock_bucket.clock,
                ),
                receive_time,
            });

            segment_index += 1;
        }

        for event in &segment.events {
            match event {
                LogEvent::Event(ev) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::Event(*ev),
                        receive_time,
                    });
                }
                LogEvent::EventWithPayload(ev, payload) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::EventWithPayload(*ev, *payload),
                        receive_time,
                    });
                }
            }

            segment_index += 1;
        }

        next_segment_id += 1;
    }

    next_segment_id
}

pub fn add_owned_report_to_entries(
    report: LogReport,
    session_id: SessionId,
    initial_segment_id: SegmentId,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<LogEntry>,
) -> u32 {
    let mut next_segment_id = initial_segment_id.0;
    let probe_id = report.probe_id;
    for segment in report.segments {
        let mut segment_index = 0;

        for clock_bucket in segment.clocks {
            log_entries_buffer.push(LogEntry {
                session_id,
                segment_id: next_segment_id.into(),
                segment_index,
                probe_id,
                data: LogEntryData::LogicalClock(
                    clock_bucket.id,
                    clock_bucket.epoch,
                    clock_bucket.clock,
                ),
                receive_time,
            });

            segment_index += 1;
        }

        for event in &segment.events {
            match event {
                modality_probe::compact_log::LogEvent::Event(ev) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::Event(*ev),
                        receive_time,
                    });
                }
                modality_probe::compact_log::LogEvent::EventWithPayload(ev, payload) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::EventWithPayload(*ev, *payload),
                        receive_time,
                    });
                }
            }

            segment_index += 1;
        }

        next_segment_id += 1;
    }

    next_segment_id
}

#[cfg(test)]
pub mod test {
    use proptest::prelude::*;

    use modality_probe::EventId;

    use super::*;

    pub fn arb_session_id() -> impl Strategy<Value = SessionId> {
        any::<u32>().prop_map_into()
    }

    pub fn arb_segment_id() -> impl Strategy<Value = SegmentId> {
        any::<u32>().prop_map_into()
    }

    pub fn arb_segment_index() -> impl Strategy<Value = u32> {
        any::<u32>()
    }
    prop_compose! {
        pub(crate) fn gen_raw_internal_event_id()(raw_id in (EventId::MAX_USER_ID + 1)..EventId::MAX_INTERNAL_ID) -> u32 {
            raw_id
        }
    }

    fn arb_event_id() -> impl Strategy<Value = EventId> {
        prop_oneof![
            gen_raw_internal_event_id().prop_map(|id| EventId::new_internal(id).unwrap()),
            gen_raw_user_event_id().prop_map(|id| EventId::new(id).unwrap()),
        ]
    }

    pub fn arb_event_mapping() -> impl Strategy<Value = EventMapping> {
        (arb_event_id(), any::<String>(), any::<String>()).prop_map(|(id, name, description)| {
            EventMapping {
                id,
                name,
                description,
            }
        })
    }

    prop_compose! {
        pub(crate) fn arb_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> ProbeId {
            ProbeId::new(raw_id).unwrap()
        }
    }

    pub(crate) fn arb_probe_epoch() -> impl Strategy<Value = ProbeEpoch> {
        any::<u16>()
    }

    pub(crate) fn arb_probe_clock() -> impl Strategy<Value = ProbeClock> {
        any::<u16>()
    }

    pub fn arb_probe_mapping() -> impl Strategy<Value = ProbeMapping> {
        (arb_probe_id(), any::<String>(), any::<String>()).prop_map(|(id, name, description)| {
            ProbeMapping {
                id,
                name,
                description,
            }
        })
    }

    pub fn arb_log_entry_data() -> impl Strategy<Value = LogEntryData> {
        let eid = arb_event_id().prop_map_into().boxed();
        let lc = (arb_probe_id(), arb_probe_epoch(), arb_probe_clock())
            .prop_map_into()
            .boxed();
        eid.prop_union(lc)
    }

    pub fn arb_datetime() -> impl Strategy<Value = DateTime<Utc>> {
        any::<i64>().prop_map(|n| Utc.timestamp_nanos(n))
    }

    pub fn arb_log_entry() -> impl Strategy<Value = LogEntry> {
        (
            arb_session_id(),
            arb_segment_id(),
            arb_segment_index(),
            arb_probe_id(),
            arb_log_entry_data(),
            arb_datetime(),
        )
            .prop_map(
                |(session_id, segment_id, segment_index, probe_id, data, receive_time)| LogEntry {
                    session_id,
                    segment_id,
                    segment_index,
                    probe_id,
                    data,
                    receive_time,
                },
            )
    }

    prop_compose! {
        pub(crate) fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
            raw_id
        }
    }

    fn arb_log_file_line() -> impl Strategy<Value = LogFileRow> {
        (
            any::<u32>(),
            any::<u32>(),
            any::<u32>(),
            test::arb_datetime(),
            any::<u32>(),
            // util::EventId requires a valid event id now.
            proptest::option::of(gen_raw_user_event_id()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<ProbeEpoch>()),
            proptest::option::of(any::<ProbeClock>()),
        )
            .prop_map(
                |(
                    session_id,
                    segment_id,
                    segment_index,
                    receive_time,
                    probe_id,
                    event_id,
                    event_payload,
                    lc_probe_id,
                    lc_probe_epoch,
                    lc_probe_clock,
                )| LogFileRow {
                    session_id,
                    segment_id,
                    segment_index,
                    receive_time,
                    probe_id,
                    event_id,
                    // The event payload can only be set if there's also
                    // an event id.
                    event_payload: if event_id.is_some() && event_payload.is_some() {
                        event_payload
                    } else {
                        None
                    },
                    lc_probe_id,
                    lc_probe_epoch,
                    lc_probe_clock,
                },
            )
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 1000, .. ProptestConfig::default()})]

        #[test]
        fn entry_to_line_round_trip(entry in test::arb_log_entry())
        {
            let line : LogFileRow = (&entry).into();
            match LogEntry::try_from(&line) {
                Err(err) => prop_assert!(false, "convert back error: {:?}", err),
                Ok(e2) => prop_assert_eq!(entry, e2),
            }
        }


        #[test]
        fn line_to_entry_round_trip(line in arb_log_file_line())
        {
            match LogEntry::try_from(&line) {
                // This should fail sometimes, but always in the same way
                Err(ReadError::InvalidContent{
                    session_id,
                    segment_id,
                    segment_index,
                    .. }) =>
                {
                    prop_assert_eq!(session_id, line.session_id.into());
                    prop_assert_eq!(segment_id, line.segment_id.into());
                    prop_assert_eq!(segment_index, u32::from(line.segment_index));
                }

                Err(err) =>
                    prop_assert!(false, "Unexpected conversion error: {:?}", err),

                Ok(entry) => {
                    let l2: LogFileRow = (&entry).into();
                    prop_assert_eq!(line, l2);
                },
            }
        }

    }
}
