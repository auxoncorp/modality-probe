use std::{
    convert::{TryFrom, TryInto},
    io,
    iter::Peekable,
    mem,
};

use chrono::prelude::*;
use err_derive::Error;
use fenced_ring_buffer::WholeEntry;
use serde::{Deserialize, Serialize};
use static_assertions::assert_eq_size;

use modality_probe::{
    log::LogEntry,
    time::{
        NanosecondResolution, Nanoseconds, NanosecondsHighBits, NanosecondsLowBits, WallClockId,
    },
    wire::{le_bytes, ReportWireError, WireReport},
    EventId, LogicalClock, ProbeEpoch, ProbeId, ProbeTicks,
};

pub mod json;

assert_eq_size!(LogEntry, u32);

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
    #[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash, Copy, Clone)]
    pub struct SessionId(pub u32);
}

newtype! {
    /// A log report sequence number
    #[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash, Copy, Clone, Ord, PartialOrd)]
    pub struct SequenceNumber(pub u64);
}

impl SequenceNumber {
    /// Get the sequence number which preceded this one.
    pub fn prev(&self) -> Self {
        SequenceNumber(self.0.saturating_sub(1))
    }
}

#[derive(Debug, Error)]
pub enum SerializationError {
    #[error(display = "Invalid probe id {:?}", _0)]
    InvalidProbeId(LogEntry),

    #[error(display = "Invalid event id {:?}", _0)]
    InvalidEventId(LogEntry),

    #[error(display = "Report wire error")]
    ReportWireError(#[error(source)] ReportWireError),

    #[error(
        display = "Too many frontier clocks ({:?}) for the wire type's u16 primitive",
        _0
    )]
    TooManyFrontierClocks(usize),

    #[error(
        display = "Too many log entries ({:?}) for the wire type's u32 primitive",
        _0
    )]
    TooManyLogEntries(usize),

    #[error(display = "Invalid time {:?}", _0)]
    InvalidTime((NanosecondsLowBits, NanosecondsHighBits)),
}

#[derive(Debug, PartialEq)]
pub struct Report {
    pub probe_id: ProbeId,
    pub probe_clock: LogicalClock,
    pub seq_num: SequenceNumber,
    pub persistent_epoch_counting: bool,
    pub time_resolution: NanosecondResolution,
    pub wall_clock_id: WallClockId,
    pub frontier_clocks: Vec<LogicalClock>,
    pub event_log: Vec<EventLogEntry>,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum EventLogEntry {
    Event(Option<Nanoseconds>, EventId),
    EventWithPayload(Option<Nanoseconds>, EventId, u32),
    TraceClock(Option<Nanoseconds>, LogicalClock),
    WallClockTime(Nanoseconds),
}

pub mod serde_ns {
    use super::Nanoseconds;
    use serde::{de, Deserialize, Serialize};

    pub fn serialize<S>(value: &Option<Nanoseconds>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if let Some(time) = value {
            time.get().serialize(serializer)
        } else {
            ().serialize(serializer)
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Option<Nanoseconds>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let v: Option<u64> = Deserialize::deserialize(deserializer)?;
        match v {
            Some(t) => {
                let t = Nanoseconds::new(t)
                    .ok_or("Invalid Nanoseconds")
                    .map_err(de::Error::custom)?;
                Ok(Some(t))
            }
            None => Ok(None),
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "Nanoseconds")]
struct NanosecondsDef(#[serde(getter = "Nanoseconds::get")] u64);

impl From<NanosecondsDef> for Nanoseconds {
    fn from(def: NanosecondsDef) -> Nanoseconds {
        Nanoseconds::new_truncate(def.0)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "NanosecondResolution")]
struct NanosecondResolutionDef(pub u32);

#[derive(Serialize, Deserialize)]
#[serde(remote = "WallClockId")]
struct WallClockIdDef(pub u16);

/// A single entry in the log
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Clone)]
pub struct ReportLogEntry {
    /// The session in which this entry was made. Used to qualify the id field.
    pub session_id: SessionId,

    /// The sequence number to which this entry belongs
    pub sequence_number: SequenceNumber,

    /// Where this entry occurs within the sequence number
    pub sequence_index: u32,

    /// The probe that supplied this entry
    pub probe_id: ProbeId,

    /// Whether or not the probe which reported this event has a
    /// persistent epoch counter.
    pub persistent_epoch_counting: bool,

    /// Time resolution
    #[serde(with = "NanosecondResolutionDef")]
    pub time_resolution: NanosecondResolution,

    /// Wall clock ID
    #[serde(with = "WallClockIdDef")]
    pub wall_clock_id: WallClockId,

    /// This entry's data; a frontier
    /// clock, event, event with payload, or a trace clock
    pub data: LogEntryData,

    /// The time this entry was received by the collector
    ///
    /// This is the collector's system clock at the time the entry data was
    /// received, not when it was created. It is stored for convenience only;
    /// the logical clock should be used for ordering messages.
    pub receive_time: DateTime<Utc>,
}

impl ReportLogEntry {
    pub fn is_frontier_clock(&self) -> bool {
        matches!(self.data, LogEntryData::FrontierClock(_))
    }
    pub fn is_internal_event(&self) -> bool {
        match self.data {
            LogEntryData::Event(_t, id) => id.is_internal(),
            LogEntryData::EventWithPayload(_t, id, _) => id.is_internal(),
            _ => false,
        }
    }

    pub fn coordinate(&self) -> String {
        // TODO(dan@auxon.io): Clocks not available here.
        // https://github.com/auxoncorp/modality-probe/issues/278
        format!(
            "{}:{}:{}:{}",
            self.session_id.0,
            self.probe_id.get_raw(),
            self.sequence_number.0,
            self.sequence_index
        )
    }
}

#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Clone)]
pub enum LogEntryData {
    FrontierClock(LogicalClock),
    Event(
        #[serde(default, with = "serde_ns")] Option<Nanoseconds>,
        EventId,
    ),
    EventWithPayload(
        #[serde(default, with = "serde_ns")] Option<Nanoseconds>,
        EventId,
        u32,
    ),
    TraceClock(
        #[serde(default, with = "serde_ns")] Option<Nanoseconds>,
        LogicalClock,
    ),
    WallClockTime(#[serde(with = "NanosecondsDef")] Nanoseconds),
}

impl LogEntryData {
    pub fn trace_clock(&self) -> Option<LogicalClock> {
        if let LogEntryData::TraceClock(_t, lc) = *self {
            Some(lc)
        } else {
            None
        }
    }
}

impl From<EventLogEntry> for LogEntryData {
    fn from(e: EventLogEntry) -> Self {
        match e {
            EventLogEntry::Event(t, id) => LogEntryData::Event(t, id),
            EventLogEntry::EventWithPayload(t, id, p) => LogEntryData::EventWithPayload(t, id, p),
            EventLogEntry::TraceClock(t, lc) => LogEntryData::TraceClock(t, lc),
            EventLogEntry::WallClockTime(t) => LogEntryData::WallClockTime(t),
        }
    }
}

/// A row in a collected trace.
#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct LogFileRow {
    pub session_id: u32,
    pub sequence_number: u64,
    pub sequence_index: u32,
    pub time_resolution: u32,
    pub wall_clock_id: u16,
    pub receive_time: DateTime<Utc>,
    pub probe_id: u32,
    pub fc_probe_id: Option<u32>,
    pub fc_probe_epoch: Option<u16>,
    pub fc_probe_clock: Option<u16>,
    pub event_id: Option<u32>,
    pub event_payload: Option<u32>,
    pub tc_probe_id: Option<u32>,
    pub tc_probe_epoch: Option<u16>,
    pub tc_probe_clock: Option<u16>,
}

impl LogFileRow {
    pub fn packed_tc_clock(&self) -> Option<u32> {
        if self.tc_probe_epoch.is_some() && self.tc_probe_clock.is_some() {
            Some(modality_probe::pack_clock_word(
                ProbeEpoch::from(self.tc_probe_epoch.expect("just checked epoch presence")),
                ProbeTicks::from(self.tc_probe_clock.expect("just checked clock presence")),
            ))
        } else {
            None
        }
    }

    pub fn packed_fc_clock(&self) -> Option<u32> {
        if self.fc_probe_epoch.is_some() && self.fc_probe_clock.is_some() {
            Some(modality_probe::pack_clock_word(
                ProbeEpoch::from(self.fc_probe_epoch.expect("just checked epoch presence")),
                ProbeTicks::from(self.fc_probe_clock.expect("just checked clock presence")),
            ))
        } else {
            None
        }
    }

    pub fn is_trace_clock(&self) -> bool {
        self.tc_probe_id.is_some() && self.tc_probe_epoch.is_some() && self.tc_probe_clock.is_some()
    }

    pub fn is_frontier_clock(&self) -> bool {
        self.fc_probe_id.is_some() && self.fc_probe_epoch.is_some() && self.fc_probe_clock.is_some()
    }

    pub fn is_event(&self) -> bool {
        self.event_id.is_some()
    }
}

pub struct ReportIter<I>
where
    I: Iterator<Item = ReportLogEntry>,
{
    report_items: Peekable<I>,
}

impl<I> ReportIter<I>
where
    I: Iterator<Item = ReportLogEntry>,
{
    pub fn new(report_items: Peekable<I>) -> Self {
        ReportIter { report_items }
    }
}

impl<I> Iterator for ReportIter<I>
where
    I: Iterator<Item = ReportLogEntry>,
{
    type Item = Report;
    fn next(&mut self) -> Option<Report> {
        let next = match self.report_items.peek() {
            Some(e) => e,
            None => return None,
        };
        let probe_id = next.probe_id;

        let seq_num = next.sequence_number;
        let mut report = Report {
            probe_id,
            probe_clock: LogicalClock {
                id: probe_id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
            persistent_epoch_counting: next.persistent_epoch_counting,
            time_resolution: next.time_resolution,
            wall_clock_id: next.wall_clock_id,
            seq_num: next.sequence_number,
            frontier_clocks: Vec::new(),
            event_log: Vec::new(),
        };

        loop {
            let next = match self.report_items.peek() {
                Some(e) => e,
                None => return Some(report),
            };
            if next.probe_id != probe_id || next.sequence_number != seq_num {
                return Some(report);
            }

            // we peeked at this item above.
            let e = self.report_items.next().unwrap();
            match e.data {
                LogEntryData::FrontierClock(lc) => {
                    let id = lc.id;
                    if id == report.probe_id {
                        report.probe_clock = lc;
                    }
                    report.frontier_clocks.push(lc);
                }
                LogEntryData::TraceClock(t, lc) => {
                    let id = lc.id;
                    report.event_log.push(EventLogEntry::TraceClock(t, lc));
                    if id == report.probe_id {
                        report.probe_clock = lc;
                    }
                }
                LogEntryData::Event(t, e) => {
                    report.event_log.push(EventLogEntry::Event(t, e));
                }
                LogEntryData::EventWithPayload(t, e, p) => {
                    report
                        .event_log
                        .push(EventLogEntry::EventWithPayload(t, e, p));
                }
                LogEntryData::WallClockTime(t) => {
                    report.event_log.push(EventLogEntry::WallClockTime(t));
                }
            }
        }
    }
}

impl From<&ReportLogEntry> for LogFileRow {
    fn from(e: &ReportLogEntry) -> LogFileRow {
        LogFileRow {
            session_id: e.session_id.0,
            sequence_number: e.sequence_number.0,
            sequence_index: e.sequence_index,
            time_resolution: e.time_resolution.into(),
            wall_clock_id: e.wall_clock_id.into(),
            probe_id: e.probe_id.get_raw(),
            fc_probe_id: match e.data {
                LogEntryData::FrontierClock(lc) => Some(lc.id.get_raw()),
                _ => None,
            },
            fc_probe_epoch: match e.data {
                LogEntryData::FrontierClock(lc) => Some(lc.epoch.0),
                _ => None,
            },
            fc_probe_clock: match e.data {
                LogEntryData::FrontierClock(lc) => Some(lc.ticks.0),
                _ => None,
            },
            event_id: match &e.data {
                LogEntryData::Event(_t, id) => Some(id.get_raw()),
                LogEntryData::EventWithPayload(_t, id, _) => Some(id.get_raw()),
                _ => None,
            },
            event_payload: match &e.data {
                LogEntryData::EventWithPayload(_t, _id, payload) => Some(*payload),
                _ => None,
            },
            tc_probe_id: match &e.data {
                LogEntryData::TraceClock(_t, lc) => Some(lc.id.get_raw()),
                _ => None,
            },
            tc_probe_epoch: match &e.data {
                LogEntryData::TraceClock(_t, lc) => Some(lc.epoch.0),
                _ => None,
            },
            tc_probe_clock: match &e.data {
                LogEntryData::TraceClock(_t, lc) => Some(lc.ticks.0),
                _ => None,
            },
            receive_time: e.receive_time,
        }
    }
}

#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error(display = "{}", message)]
    InvalidContent {
        session_id: SessionId,
        sequence_number: SequenceNumber,
        sequence_index: u32,
        message: &'static str,
    },
    #[error(display = "{}", _0)]
    Serialization(String),
    #[error(display = "IO error: {}", _0)]
    Io(String),
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::Io(format!("{}", e))
    }
}

impl TryFrom<&LogFileRow> for ReportLogEntry {
    type Error = Error;

    fn try_from(l: &LogFileRow) -> Result<ReportLogEntry, Self::Error> {
        let session_id: SessionId = l.session_id.into();
        let sequence_number: SequenceNumber = l.sequence_number.into();
        let sequence_index: u32 = l.sequence_index;
        let time_resolution = l.time_resolution.into();
        let wall_clock_id = l.wall_clock_id.into();

        let data = if let Some(fc_probe_id) = l.fc_probe_id {
            match (l.fc_probe_epoch, l.fc_probe_clock) {
                (Some(epoch), Some(clock)) => {
                    LogEntryData::FrontierClock(
                        LogicalClock {
                            id: fc_probe_id.try_into().map_err(|_e|
                                Error::InvalidContent {
                                    session_id,
                                    sequence_number,
                                    sequence_index,
                                    message: "When fc_probe_id is present, it must be a valid modality_probe::ProbeId",
                                })?,
                            epoch: epoch.into(),
                            ticks: clock.into(),
                        }
                    )
                }
                (None, _) => {
                    return Err(Error::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When fc_probe_id is present, fc_probe_epoch must also be present",
                    });
                },
                (_, None) => {
                    return Err(Error::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When fc_probe_id is present, fc_probe_clock must also be present",
                    });
                },
            }
        } else if let Some(event_id) = l.event_id {
            if l.fc_probe_id.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_id must be empty",
                });
            } else if l.fc_probe_epoch.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_epoch must be empty",
                });
            } else if l.fc_probe_clock.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_clock must be empty",
                });
            } else if l.tc_probe_id.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_id must be empty",
                });
            } else if l.tc_probe_epoch.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_epoch must be empty",
                });
            } else if l.tc_probe_clock.is_some() {
                return Err(Error::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_clock must be empty",
                });
            }

            let event_id = event_id.try_into().map_err(|_e| Error::InvalidContent {
                session_id,
                sequence_number,
                sequence_index,
                message: "Invalid event id",
            })?;

            if let Some(payload) = l.event_payload {
                LogEntryData::EventWithPayload(None, event_id, payload)
            } else {
                LogEntryData::Event(None, event_id)
            }
        } else if let Some(tc_probe_id) = l.tc_probe_id {
            match (l.tc_probe_epoch, l.tc_probe_clock) {
                (Some(epoch), Some(clock)) => {
                    LogEntryData::TraceClock(None,
                        LogicalClock {
                            id: tc_probe_id.try_into().map_err(|_e|
                                Error::InvalidContent {
                                    session_id,
                                    sequence_number,
                                    sequence_index,
                                    message: "When tc_probe_id is present, it must be a valid modality_probe::ProbeId",
                                })?,
                            epoch: epoch.into(),
                            ticks: clock.into(),
                        }
                    )
                }
                (None, _) => {
                    return Err(Error::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When tc_probe_id is present, tc_probe_epoch must also be present",
                    });
                },
                (_, None) => {
                    return Err(Error::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When tc_probe_id is present, tc_probe_clock must also be present",
                    });
                },
            }
        } else {
            return Err(Error::InvalidContent {
                session_id,
                sequence_number,
                sequence_index,
                message: "Either fc_probe_id, event_id, or tc_probe_id must be preset",
            });
        };

        Ok(ReportLogEntry {
            session_id,
            sequence_number,
            sequence_index,
            persistent_epoch_counting: false,
            time_resolution,
            wall_clock_id,
            probe_id: l.probe_id.try_into().map_err(|_e| Error::InvalidContent {
                session_id,
                sequence_number,
                sequence_index,
                message: "probe_id must be a valid modality_probe::ProbeId",
            })?,
            data,
            receive_time: l.receive_time,
        })
    }
}

pub fn add_log_report_to_entries(
    log_report: &Report,
    session_id: SessionId,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<ReportLogEntry>,
) {
    let probe_id = log_report.probe_id;
    let sequence_number = log_report.seq_num;
    let time_resolution = log_report.time_resolution;
    let wall_clock_id = log_report.wall_clock_id;
    let mut sequence_index = 0;

    for fc in &log_report.frontier_clocks {
        log_entries_buffer.push(ReportLogEntry {
            session_id,
            sequence_number,
            sequence_index,
            time_resolution,
            wall_clock_id,
            probe_id,
            persistent_epoch_counting: log_report.persistent_epoch_counting,
            data: LogEntryData::FrontierClock(*fc),
            receive_time,
        });
        sequence_index += 1;
    }

    for event in &log_report.event_log {
        log_entries_buffer.push(ReportLogEntry {
            session_id,
            sequence_number,
            sequence_index,
            time_resolution,
            wall_clock_id,
            probe_id,
            persistent_epoch_counting: log_report.persistent_epoch_counting,
            data: LogEntryData::from(*event),
            receive_time,
        });
        sequence_index += 1;
    }
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
            seq_num: report.seq_num().into(),
            persistent_epoch_counting: report.persistent_epoch_counting(),
            time_resolution: report.time_resolution(),
            wall_clock_id: report.wall_clock_id(),
            frontier_clocks: vec![],
            event_log: vec![],
        };

        let payload_len = report.payload_len();
        let payload = &report.payload()[..payload_len];
        let clocks_len = report.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let mut probe_id = None;
        for u32_bytes in payload[..clocks_len].chunks_exact(mem::size_of::<LogEntry>()) {
            let raw = le_bytes::read_u32(u32_bytes);
            if probe_id.is_none() {
                let entry = unsafe { LogEntry::new_unchecked(raw) };
                if entry.has_clock_bit_set() {
                    probe_id = Some(
                        ProbeId::new(entry.interpret_as_logical_clock_probe_id())
                            .ok_or_else(|| SerializationError::InvalidProbeId(entry))?,
                    );
                }
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

        let mut paired_wall_clock_time = None;
        let mut interpret_next_as = Next::DontKnow;
        for u32_bytes in payload[clocks_len..].chunks_exact(mem::size_of::<LogEntry>()) {
            let raw = le_bytes::read_u32(u32_bytes);
            match interpret_next_as {
                Next::DontKnow => {
                    let raw_entry = unsafe { LogEntry::new_unchecked(raw) };
                    if raw_entry.has_clock_bit_set() {
                        interpret_next_as = Next::Clock(
                            ProbeId::new(raw_entry.interpret_as_logical_clock_probe_id())
                                .ok_or_else(|| SerializationError::InvalidProbeId(raw_entry))?,
                        );
                    } else if raw_entry.has_event_with_payload_bit_set() {
                        interpret_next_as = Next::Payload(
                            raw_entry
                                .interpret_as_event_id()
                                .ok_or_else(|| SerializationError::InvalidEventId(raw_entry))?,
                        );
                    } else if raw_entry.has_wall_clock_time_bits_set() {
                        if raw_entry.has_wall_clock_time_paired_bit_set() {
                            interpret_next_as =
                                Next::PairedWallClockTimeLowBits(NanosecondsHighBits(
                                    raw_entry.interpret_as_wall_clock_time_high_bits(),
                                ));
                        } else {
                            interpret_next_as =
                                Next::UnpairedWallClockTimeLowBits(NanosecondsHighBits(
                                    raw_entry.interpret_as_wall_clock_time_high_bits(),
                                ));
                        }
                    } else {
                        owned_report.event_log.push(EventLogEntry::Event(
                            paired_wall_clock_time.take(),
                            raw_entry
                                .interpret_as_event_id()
                                .ok_or_else(|| SerializationError::InvalidEventId(raw_entry))?,
                        ));
                    }
                }
                Next::Clock(id) => {
                    let (epoch, ticks) = modality_probe::unpack_clock_word(raw);
                    owned_report.event_log.push(EventLogEntry::TraceClock(
                        paired_wall_clock_time.take(),
                        LogicalClock { id, epoch, ticks },
                    ));
                    interpret_next_as = Next::DontKnow;
                }
                Next::Payload(id) => {
                    if id == EventId::EVENT_LOG_ITEMS_MISSED {
                        eprintln!(
                            "ProbeId {} missed {} log entries; consider increasing its backing storage size or its reporting frequency",
                            owned_report.probe_id.get(),
                            raw
                        );
                    }
                    owned_report.event_log.push(EventLogEntry::EventWithPayload(
                        paired_wall_clock_time.take(),
                        id,
                        raw,
                    ));
                    interpret_next_as = Next::DontKnow;
                }
                Next::PairedWallClockTimeLowBits(high_bits) => {
                    let low_bits = NanosecondsLowBits(raw);
                    let t = Nanoseconds::from_parts(low_bits, high_bits)
                        .ok_or_else(|| SerializationError::InvalidTime((low_bits, high_bits)))?;
                    paired_wall_clock_time = Some(t);
                    interpret_next_as = Next::DontKnow;
                }
                Next::UnpairedWallClockTimeLowBits(high_bits) => {
                    let low_bits = NanosecondsLowBits(raw);
                    let t = Nanoseconds::from_parts(low_bits, high_bits)
                        .ok_or_else(|| SerializationError::InvalidTime((low_bits, high_bits)))?;
                    owned_report.event_log.push(EventLogEntry::WallClockTime(t));
                    interpret_next_as = Next::DontKnow;
                }
            }
        }
        Ok(owned_report)
    }
}

#[derive(Debug)]
enum Next {
    Clock(ProbeId),
    Payload(EventId),
    PairedWallClockTimeLowBits(NanosecondsHighBits),
    UnpairedWallClockTimeLowBits(NanosecondsHighBits),
    DontKnow,
}

impl Report {
    /// Try to create a report from a list of log entries
    pub fn try_from_log(
        source_clock: LogicalClock,
        seq_num: u64,
        frontier_clocks: Vec<LogicalClock>,
        log: &[WholeEntry<LogEntry>],
    ) -> Result<Self, SerializationError> {
        let mut owned_report = Report {
            probe_id: source_clock.id,
            probe_clock: source_clock,
            seq_num: SequenceNumber(seq_num),
            frontier_clocks,
            event_log: vec![],
            persistent_epoch_counting: false,
            time_resolution: NanosecondResolution::UNSPECIFIED,
            wall_clock_id: WallClockId::default(),
        };
        let mut paired_wall_clock_time = None;

        for entry in log {
            match entry {
                WholeEntry::Single(ev) => {
                    owned_report.event_log.push(EventLogEntry::Event(
                        paired_wall_clock_time.take(),
                        ev.interpret_as_event_id()
                            .ok_or_else(|| SerializationError::InvalidEventId(*ev))?,
                    ));
                }
                WholeEntry::Double(first, second) => {
                    if first.has_clock_bit_set() {
                        let id = ProbeId::new(first.interpret_as_logical_clock_probe_id())
                            .ok_or_else(|| SerializationError::InvalidProbeId(*first))?;
                        let (epoch, ticks) = modality_probe::unpack_clock_word(second.raw());
                        owned_report.event_log.push(EventLogEntry::TraceClock(
                            paired_wall_clock_time.take(),
                            LogicalClock { id, epoch, ticks },
                        ));
                    } else if first.has_wall_clock_time_bits_set() {
                        let high_bits = first.interpret_as_wall_clock_time_high_bits().into();
                        let low_bits = second.raw().into();
                        let t = Nanoseconds::from_parts(low_bits, high_bits).ok_or_else(|| {
                            SerializationError::InvalidTime((low_bits, high_bits))
                        })?;
                        if first.has_wall_clock_time_paired_bit_set() {
                            paired_wall_clock_time = Some(t);
                        } else {
                            owned_report.event_log.push(EventLogEntry::WallClockTime(t));
                        }
                    } else {
                        debug_assert!(first.has_event_with_payload_bit_set());
                        let ev = first
                            .interpret_as_event_id()
                            .ok_or_else(|| SerializationError::InvalidEventId(*first))?;
                        let payload = second.raw();
                        owned_report.event_log.push(EventLogEntry::EventWithPayload(
                            paired_wall_clock_time.take(),
                            ev,
                            payload,
                        ));
                    }
                }
            }
        }
        Ok(owned_report)
    }

    pub fn write_into_le_bytes(&self, bytes: &mut [u8]) -> Result<usize, SerializationError> {
        if self.frontier_clocks.len() > std::u16::MAX as usize {
            return Err(SerializationError::TooManyFrontierClocks(
                self.frontier_clocks.len(),
            ));
        }

        let mut wire = WireReport::new_unchecked(bytes);
        wire.check_len()?;
        wire.set_fingerprint();
        wire.set_probe_id(self.probe_id);
        wire.set_clock(modality_probe::pack_clock_word(
            self.probe_clock.epoch,
            self.probe_clock.ticks,
        ));
        wire.set_seq_num(self.seq_num.0);
        wire.set_persistent_epoch_counting(self.persistent_epoch_counting);
        wire.set_time_resolution(self.time_resolution);
        wire.set_wall_clock_id(self.wall_clock_id);
        wire.set_n_clocks(self.frontier_clocks.len() as _);

        let num_u32_entries: usize = self
            .event_log
            .iter()
            .map(|e| match e {
                EventLogEntry::Event(t, _) => {
                    1 + t
                        .map(|_| mem::size_of::<Nanoseconds>() / mem::size_of::<u32>())
                        .unwrap_or(0)
                }
                EventLogEntry::EventWithPayload(t, _, _) => {
                    2 + t
                        .map(|_| mem::size_of::<Nanoseconds>() / mem::size_of::<u32>())
                        .unwrap_or(0)
                }
                EventLogEntry::TraceClock(t, _) => {
                    (mem::size_of::<LogicalClock>() / mem::size_of::<u32>())
                        + t.map(|_| mem::size_of::<Nanoseconds>() / mem::size_of::<u32>())
                            .unwrap_or(0)
                }
                EventLogEntry::WallClockTime(_) => {
                    mem::size_of::<Nanoseconds>() / mem::size_of::<u32>()
                }
            })
            .sum();

        if num_u32_entries > std::u32::MAX as usize {
            return Err(SerializationError::TooManyLogEntries(num_u32_entries));
        }

        wire.set_n_log_entries(num_u32_entries as _);
        wire.check_payload_len()?;

        let payload = wire.payload_mut();
        let n_clock_bytes = self.frontier_clocks.len() * mem::size_of::<LogicalClock>();
        for (src_clock, dest_bytes) in self
            .frontier_clocks
            .iter()
            .zip(payload[..n_clock_bytes].chunks_exact_mut(mem::size_of::<LogicalClock>()))
        {
            let (entry_a, entry_b) = LogEntry::clock(*src_clock);
            le_bytes::write_u32(&mut dest_bytes[..4], entry_a.raw());
            le_bytes::write_u32(&mut dest_bytes[4..8], entry_b.raw());
        }

        let write_paired_time = |t: &Option<Nanoseconds>, buffer: &mut [u8]| -> usize {
            if let Some(t) = t {
                let (entry_a, entry_b) = LogEntry::paired_wall_clock_time(*t);
                let mut bc = 0;
                le_bytes::write_u32(&mut buffer[bc..], entry_a.raw());
                bc += mem::size_of::<u32>();
                le_bytes::write_u32(&mut buffer[bc..], entry_b.raw());
                bc += mem::size_of::<u32>();
                bc
            } else {
                0
            }
        };

        let mut byte_cursor = n_clock_bytes;
        for src_entry in self.event_log.iter() {
            match src_entry {
                EventLogEntry::Event(t, id) => {
                    byte_cursor += write_paired_time(t, &mut payload[byte_cursor..]);
                    let entry = LogEntry::event(*id);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
                EventLogEntry::EventWithPayload(t, id, p) => {
                    byte_cursor += write_paired_time(t, &mut payload[byte_cursor..]);
                    let (entry_a, entry_b) = LogEntry::event_with_payload(*id, *p);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_a.raw());
                    byte_cursor += mem::size_of::<u32>();
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_b.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
                EventLogEntry::TraceClock(t, lc) => {
                    byte_cursor += write_paired_time(t, &mut payload[byte_cursor..]);
                    let (entry_a, entry_b) = LogEntry::clock(*lc);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_a.raw());
                    byte_cursor += mem::size_of::<u32>();
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_b.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
                EventLogEntry::WallClockTime(t) => {
                    let (entry_a, entry_b) = LogEntry::unpaired_wall_clock_time(*t);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_a.raw());
                    byte_cursor += mem::size_of::<u32>();
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_b.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
            }
        }

        Ok(WireReport::<&[u8]>::buffer_len(
            self.frontier_clocks.len(),
            num_u32_entries as _,
        ))
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use modality_probe::*;
    use pretty_assertions::assert_eq;
    use proptest::prelude::*;
    use proptest::std_facade::*;
    use std::convert::TryFrom;
    use std::mem::MaybeUninit;

    pub fn arb_session_id() -> impl Strategy<Value = SessionId> {
        any::<u32>().prop_map_into()
    }

    pub fn arb_sequence_number() -> impl Strategy<Value = SequenceNumber> {
        any::<u64>().prop_map_into()
    }

    pub fn arb_sequence_index() -> impl Strategy<Value = u32> {
        any::<u32>()
    }

    prop_compose! {
        pub fn gen_raw_internal_event_id()(
            raw_id in (EventId::MAX_USER_ID + 1)..EventId::MAX_INTERNAL_ID
        ) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
            raw_id
        }
    }

    pub fn arb_event_id() -> impl Strategy<Value = EventId> {
        prop_oneof![
            gen_raw_internal_event_id().prop_map(|id| EventId::new_internal(id).unwrap()),
            gen_raw_user_event_id().prop_map(|id| EventId::new(id).unwrap()),
        ]
    }

    prop_compose! {
        pub fn arb_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> ProbeId {
            ProbeId::new(raw_id).unwrap()
        }
    }

    prop_compose! {
        pub fn gen_wall_clock_time()
            (raw_time in 0_u64..=Nanoseconds::MAX.get()) -> Nanoseconds {
            Nanoseconds::new(raw_time).unwrap()
        }
    }

    prop_compose! {
        pub fn gen_maybe_wall_clock_time()
            (raw_time in proptest::num::u64::ANY) -> Option<Nanoseconds> {
            Nanoseconds::new(raw_time)
        }
    }

    pub fn arb_persistent_epoch_counting() -> impl Strategy<Value = bool> {
        any::<bool>()
    }

    pub fn arb_wall_clock_id() -> impl Strategy<Value = WallClockId> {
        any::<u16>().prop_map_into()
    }

    pub fn arb_time_resolution() -> impl Strategy<Value = NanosecondResolution> {
        any::<u32>().prop_map_into()
    }

    pub fn arb_probe_epoch() -> impl Strategy<Value = ProbeEpoch> {
        any::<ProbeEpoch>()
    }

    pub fn arb_probe_clock() -> impl Strategy<Value = ProbeTicks> {
        any::<ProbeTicks>()
    }

    pub fn arb_datetime() -> impl Strategy<Value = DateTime<Utc>> {
        any::<i64>().prop_map(|n| Utc.timestamp_nanos(n))
    }

    pub fn arb_logical_clock() -> impl Strategy<Value = LogicalClock> {
        (arb_probe_id(), arb_probe_epoch(), arb_probe_clock())
            .prop_map(|(id, epoch, ticks)| LogicalClock { id, epoch, ticks })
    }

    prop_compose! {
        pub fn gen_frontier_clocks(max_clocks: usize)
        (vec in proptest::collection::vec(arb_logical_clock(), 0..max_clocks))
        -> Vec<LogicalClock> {
            vec
        }
    }

    pub fn arb_log_entry_data() -> impl Strategy<Value = LogEntryData> {
        let fc = arb_logical_clock()
            .prop_map(|lc| LogEntryData::FrontierClock(lc))
            .boxed();
        let eid = (gen_maybe_wall_clock_time(), arb_event_id())
            .prop_map(|(t, id)| LogEntryData::Event(t, id))
            .boxed();
        let eid_wp = (gen_maybe_wall_clock_time(), arb_event_id(), any::<u32>())
            .prop_map(|(t, id, p)| LogEntryData::EventWithPayload(t, id, p))
            .boxed();
        let tc = (gen_maybe_wall_clock_time(), arb_logical_clock())
            .prop_map(|(t, lc)| LogEntryData::TraceClock(t, lc))
            .boxed();
        let wct = gen_wall_clock_time()
            .prop_map(|t| LogEntryData::WallClockTime(t))
            .boxed();
        fc.prop_union(eid).or(eid_wp).or(tc).or(wct)
    }

    pub fn arb_event_log_entry() -> impl Strategy<Value = EventLogEntry> {
        let tc = (gen_maybe_wall_clock_time(), arb_logical_clock())
            .prop_map(|(t, lc)| EventLogEntry::TraceClock(t, lc))
            .boxed();
        let eid = (gen_maybe_wall_clock_time(), arb_event_id())
            .prop_map(|(t, id)| EventLogEntry::Event(t, id))
            .boxed();
        let eid_wp = (gen_maybe_wall_clock_time(), arb_event_id(), any::<u32>())
            .prop_map(|(t, id, p)| EventLogEntry::EventWithPayload(t, id, p))
            .boxed();
        let wct = gen_wall_clock_time()
            .prop_map(|t| EventLogEntry::WallClockTime(t))
            .boxed();
        tc.prop_union(eid).or(eid_wp).or(wct)
    }

    prop_compose! {
        pub fn gen_event_log(max_entries: usize)
        (vec in proptest::collection::vec(arb_event_log_entry(), 0..max_entries))
        -> Vec<EventLogEntry> {
            vec
        }
    }

    pub fn arb_log_entry() -> impl Strategy<Value = ReportLogEntry> {
        (
            arb_session_id(),
            arb_sequence_number(),
            arb_sequence_index(),
            arb_probe_id(),
            arb_log_entry_data(),
            arb_datetime(),
            any::<bool>(),
            arb_time_resolution(),
            arb_wall_clock_id(),
        )
            .prop_map(
                |(
                    session_id,
                    sequence_number,
                    sequence_index,
                    probe_id,
                    data,
                    receive_time,
                    persistent_epoch_counting,
                    time_resolution,
                    wall_clock_id,
                )| {
                    ReportLogEntry {
                        session_id,
                        sequence_number,
                        sequence_index,
                        probe_id,
                        persistent_epoch_counting,
                        time_resolution,
                        wall_clock_id,
                        data,
                        receive_time,
                    }
                },
            )
    }

    prop_compose! {
        pub fn gen_report(
            max_frontier_clocks: usize,
            max_log_entries: usize)
            (
                probe_id in arb_probe_id(),
                probe_clock in arb_logical_clock(),
                seq_num in arb_sequence_number(),
                frontier_clocks in gen_frontier_clocks(max_frontier_clocks),
                event_log in gen_event_log(max_log_entries),
                persistent_epoch_counting in arb_persistent_epoch_counting(),
                time_resolution in arb_time_resolution(),
                wall_clock_id in arb_wall_clock_id(),
             ) -> Report {
                Report {
                    probe_id,
                    probe_clock,
                    seq_num,
                    persistent_epoch_counting,
                    time_resolution,
                    wall_clock_id,
                    frontier_clocks,
                    event_log,
                }
            }
    }

    #[test]
    fn report_e2e() {
        let mut storage1 = vec![MaybeUninit::new(0); 1024];
        let mut p1 = modality_probe::ModalityProbe::new_with_storage(
            &mut storage1,
            ProbeId::new(1).unwrap(),
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        let mut storage2 = vec![MaybeUninit::new(0); 1024];
        let mut p2 = modality_probe::ModalityProbe::new_with_storage(
            &mut storage2,
            ProbeId::new(2).unwrap(),
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        p1.record_event(EventId::new(1).unwrap());
        p1.record_event_with_time(EventId::new(2).unwrap(), Nanoseconds::new(10).unwrap());
        p1.record_time(Nanoseconds::new(15).unwrap());
        let mut report_dest = vec![0; 512];
        let n_bytes = p1.report(&mut report_dest).unwrap().unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes.get()]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(1).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                seq_num: 0.into(),
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    EventLogEntry::TraceClock(
                        None,
                        LogicalClock {
                            id: ProbeId::new(1).unwrap(),
                            epoch: ProbeEpoch(0),
                            ticks: ProbeTicks(0),
                        }
                    ),
                    EventLogEntry::Event(None, EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(None, EventId::new(1).unwrap()),
                    EventLogEntry::Event(Nanoseconds::new(10), EventId::new(2).unwrap()),
                    EventLogEntry::WallClockTime(Nanoseconds::new(15).unwrap()),
                ],
            }
        );

        let bytes_written = o_report.write_into_le_bytes(&mut report_dest[..]).unwrap();
        let i_report = Report::try_from(&report_dest[..bytes_written]).unwrap();
        assert_eq!(o_report, i_report);

        let snap = p1.produce_snapshot();
        p2.record_event(EventId::new(2).unwrap());
        p2.merge_snapshot(&snap).unwrap();
        let n_bytes = p1.report(&mut report_dest).unwrap().unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes.get()]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(1).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
                seq_num: 1.into(),
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    EventLogEntry::Event(None, EventId::EVENT_PRODUCED_EXTERNAL_REPORT),
                    EventLogEntry::TraceClock(
                        None,
                        LogicalClock {
                            id: ProbeId::new(1).unwrap(),
                            epoch: ProbeEpoch(0),
                            ticks: ProbeTicks(1),
                        }
                    )
                ],
            }
        );

        let bytes_written = o_report.write_into_le_bytes(&mut report_dest[..]).unwrap();
        let i_report = Report::try_from(&report_dest[..bytes_written]).unwrap();
        assert_eq!(o_report, i_report);

        p2.record_time(Nanoseconds::new(9).unwrap());
        p2.record_event(EventId::new(7).unwrap());
        p2.record_event_with_payload_with_time(
            EventId::new(8).unwrap(),
            10,
            Nanoseconds::new(12).unwrap(),
        );
        let n_bytes = p2.report(&mut report_dest).unwrap().unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes.get()]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(2).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
                seq_num: 0.into(),
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    EventLogEntry::TraceClock(
                        None,
                        LogicalClock {
                            id: ProbeId::new(2).unwrap(),
                            epoch: ProbeEpoch(0),
                            ticks: ProbeTicks(0),
                        }
                    ),
                    EventLogEntry::Event(None, EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(None, EventId::new(2).unwrap()),
                    EventLogEntry::TraceClock(
                        None,
                        LogicalClock {
                            id: ProbeId::new(2).unwrap(),
                            epoch: ProbeEpoch(0),
                            ticks: ProbeTicks(1),
                        }
                    ),
                    EventLogEntry::TraceClock(
                        None,
                        LogicalClock {
                            id: ProbeId::new(1).unwrap(),
                            epoch: ProbeEpoch(0),
                            ticks: ProbeTicks(0),
                        }
                    ),
                    EventLogEntry::WallClockTime(Nanoseconds::new(9).unwrap()),
                    EventLogEntry::Event(None, EventId::new(7).unwrap(),),
                    EventLogEntry::EventWithPayload(
                        Nanoseconds::new(12),
                        EventId::new(8).unwrap(),
                        10
                    ),
                ],
            }
        );

        let bytes_written = o_report.write_into_le_bytes(&mut report_dest[..]).unwrap();
        let i_report = Report::try_from(&report_dest[..bytes_written]).unwrap();
        assert_eq!(o_report, i_report);
    }

    proptest! {
        #[test]
        fn round_trip_serialization(
            mut report in gen_report(256, 512)
        ) {
            // Need to make sure probe_clock.id and probe_id are the same
            report.probe_clock.id = report.probe_id;

            const EXTRA_JUNK: usize = 256;
            const MEGABYTE: usize = 1024*1024;
            let mut bytes = vec![0u8; MEGABYTE + EXTRA_JUNK];
            let bytes_written = report.write_into_le_bytes(&mut bytes[..MEGABYTE]).unwrap();
            prop_assert!(bytes_written > 0 && bytes_written <= bytes.len());

            match Report::try_from(&bytes[..bytes_written+EXTRA_JUNK]) {
                Err(e) => prop_assert!(false, "Report::try_from(bytes) error: {:?}", e),
                Ok(r) => prop_assert_eq!(report, r),
            }
        }
    }
}
