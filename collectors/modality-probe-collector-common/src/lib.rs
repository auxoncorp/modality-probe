use std::{
    convert::{TryFrom, TryInto},
    iter::Peekable,
    mem,
};

use chrono::prelude::*;
use err_derive::Error;
use static_assertions::assert_eq_size;

use modality_probe::{
    log::LogEntry,
    wire::{le_bytes, ReportWireError, WireReport},
    EventId, LogicalClock, ProbeEpoch, ProbeId, ProbeTicks,
};

pub mod csv;

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
    #[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
    pub struct SessionId(pub u32);
}

newtype! {
    /// A log report sequence number
    #[derive(Debug, Eq, PartialEq, Hash, Copy, Clone)]
    pub struct SequenceNumber(pub u64);
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
}

#[derive(Debug, PartialEq)]
pub struct Report {
    pub probe_id: ProbeId,
    pub probe_clock: LogicalClock,
    pub seq_num: SequenceNumber,
    pub frontier_clocks: Vec<LogicalClock>,
    pub event_log: Vec<EventLogEntry>,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum EventLogEntry {
    Event(EventId),
    EventWithPayload(EventId, u32),
    TraceClock(LogicalClock),
}

/// A single entry in the log
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ReportLogEntry {
    /// The session in which this entry was made. Used to qualify the id field.
    pub session_id: SessionId,

    /// The sequence number to which this entry belongs
    pub sequence_number: SequenceNumber,

    /// Where this entry occurs within the sequence number
    pub sequence_index: u32,

    /// The probe that supplied this entry
    pub probe_id: ProbeId,

    /// This entry's data; a frontier clock, event, event with payload, or a trace clock
    pub data: LogEntryData,

    /// The time this entry was received by the collector
    ///
    /// This is the collector's system clock at the time the entry data was
    /// received, not when it was created. It is stored for convenience only;
    /// the logical clock should be used for ordering messages.
    pub receive_time: DateTime<Utc>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LogEntryData {
    FrontierClock(LogicalClock),
    Event(EventId),
    EventWithPayload(EventId, u32),
    TraceClock(LogicalClock),
}

impl From<EventLogEntry> for LogEntryData {
    fn from(e: EventLogEntry) -> Self {
        match e {
            EventLogEntry::Event(id) => LogEntryData::Event(id),
            EventLogEntry::EventWithPayload(id, p) => LogEntryData::EventWithPayload(id, p),
            EventLogEntry::TraceClock(lc) => LogEntryData::TraceClock(lc),
        }
    }
}

/// A row in a collected trace.
#[derive(Debug, serde::Serialize, serde::Deserialize, Eq, PartialEq)]
pub struct LogFileRow {
    pub session_id: u32,
    pub sequence_number: u64,
    pub sequence_index: u32,
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

pub struct ReportIter<I, E>
where
    I: Iterator<Item = Result<LogFileRow, E>>,
    E: std::error::Error,
{
    report_items: Peekable<I>,
    // If this iterator encounters an error while accumulating a
    // report, it stops in place, rendering it unusable. By storing
    // that error, we can keep the iterator from being used again by
    // just returning that error for any `next` calls.
    error: Option<ReadError>,
}

impl<I, E> ReportIter<I, E>
where
    I: Iterator<Item = Result<LogFileRow, E>>,
    E: std::error::Error,
{
    pub fn new(report_items: Peekable<I>) -> Self {
        ReportIter {
            report_items,
            error: None,
        }
    }
}

impl<I, E> Iterator for ReportIter<I, E>
where
    I: Iterator<Item = Result<LogFileRow, E>>,
    E: std::error::Error,
    for<'a> &'a E: Into<ReadError>,
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

impl From<&ReportLogEntry> for LogFileRow {
    fn from(e: &ReportLogEntry) -> LogFileRow {
        LogFileRow {
            session_id: e.session_id.0,
            sequence_number: e.sequence_number.0,
            sequence_index: e.sequence_index,
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
                LogEntryData::Event(id) => Some(id.get_raw()),
                LogEntryData::EventWithPayload(id, _) => Some(id.get_raw()),
                _ => None,
            },
            event_payload: match &e.data {
                LogEntryData::EventWithPayload(_, payload) => Some(*payload),
                _ => None,
            },
            tc_probe_id: match &e.data {
                LogEntryData::TraceClock(lc) => Some(lc.id.get_raw()),
                _ => None,
            },
            tc_probe_epoch: match &e.data {
                LogEntryData::TraceClock(lc) => Some(lc.epoch.0),
                _ => None,
            },
            tc_probe_clock: match &e.data {
                LogEntryData::TraceClock(lc) => Some(lc.ticks.0),
                _ => None,
            },
            receive_time: e.receive_time,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ReadError {
    InvalidContent {
        session_id: SessionId,
        sequence_number: SequenceNumber,
        sequence_index: u32,
        message: &'static str,
    },
    Serialization(String),
}

impl TryFrom<&LogFileRow> for ReportLogEntry {
    type Error = ReadError;

    fn try_from(l: &LogFileRow) -> Result<ReportLogEntry, Self::Error> {
        let session_id: SessionId = l.session_id.into();
        let sequence_number: SequenceNumber = l.sequence_number.into();
        let sequence_index: u32 = l.sequence_index;

        let data = if let Some(fc_probe_id) = l.fc_probe_id {
            match (l.fc_probe_epoch, l.fc_probe_clock) {
                (Some(epoch), Some(clock)) => {
                    LogEntryData::FrontierClock(
                        LogicalClock {
                            id: fc_probe_id.try_into().map_err(|_e|
                                ReadError::InvalidContent {
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
                    return Err(ReadError::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When fc_probe_id is present, fc_probe_epoch must also be present",
                    });
                },
                (_, None) => {
                    return Err(ReadError::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When fc_probe_id is present, fc_probe_clock must also be present",
                    });
                },
            }
        } else if let Some(event_id) = l.event_id {
            if l.fc_probe_id.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_id must be empty",
                });
            } else if l.fc_probe_epoch.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_epoch must be empty",
                });
            } else if l.fc_probe_clock.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, fc_probe_clock must be empty",
                });
            } else if l.tc_probe_id.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_id must be empty",
                });
            } else if l.tc_probe_epoch.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_epoch must be empty",
                });
            } else if l.tc_probe_clock.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "When event_id is present, tc_probe_clock must be empty",
                });
            }

            let event_id = event_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
                    session_id,
                    sequence_number,
                    sequence_index,
                    message: "Invalid event id",
                })?;

            if let Some(payload) = l.event_payload {
                LogEntryData::EventWithPayload(event_id, payload)
            } else {
                LogEntryData::Event(event_id)
            }
        } else if let Some(tc_probe_id) = l.tc_probe_id {
            match (l.tc_probe_epoch, l.tc_probe_clock) {
                (Some(epoch), Some(clock)) => {
                    LogEntryData::TraceClock(
                        LogicalClock {
                            id: tc_probe_id.try_into().map_err(|_e|
                                ReadError::InvalidContent {
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
                    return Err(ReadError::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When tc_probe_id is present, tc_probe_epoch must also be present",
                    });
                },
                (_, None) => {
                    return Err(ReadError::InvalidContent {
                        session_id,
                        sequence_number,
                        sequence_index,
                        message: "When tc_probe_id is present, tc_probe_clock must also be present",
                    });
                },
            }
        } else {
            return Err(ReadError::InvalidContent {
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
            probe_id: l
                .probe_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
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
    let mut sequence_index = 0;

    for fc in &log_report.frontier_clocks {
        log_entries_buffer.push(ReportLogEntry {
            session_id,
            sequence_number,
            sequence_index,
            probe_id,
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
            probe_id,
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
            frontier_clocks: vec![],
            event_log: vec![],
        };

        let clocks_len = report.n_clocks() as usize * mem::size_of::<LogicalClock>();
        let mut probe_id = None;
        let payload = report.payload();
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
                    } else {
                        owned_report.event_log.push(EventLogEntry::Event(
                            raw_entry
                                .interpret_as_event_id()
                                .ok_or_else(|| SerializationError::InvalidEventId(raw_entry))?,
                        ));
                    }
                }
                Next::Clock(id) => {
                    let (epoch, ticks) = modality_probe::unpack_clock_word(raw);
                    owned_report
                        .event_log
                        .push(EventLogEntry::TraceClock(LogicalClock { id, epoch, ticks }));
                    interpret_next_as = Next::DontKnow;
                }
                Next::Payload(id) => {
                    owned_report
                        .event_log
                        .push(EventLogEntry::EventWithPayload(id, raw));
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
    DontKnow,
}

impl Report {
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
        wire.set_n_clocks(self.frontier_clocks.len() as _);

        let num_u32_entries: usize = self
            .event_log
            .iter()
            .map(|e| match e {
                EventLogEntry::Event(_) => 1,
                EventLogEntry::EventWithPayload(_, _) => 2,
                EventLogEntry::TraceClock(_) => {
                    mem::size_of::<LogicalClock>() / mem::size_of::<u32>()
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

        let mut byte_cursor = n_clock_bytes;
        for src_entry in self.event_log.iter() {
            match src_entry {
                EventLogEntry::Event(id) => {
                    let entry = LogEntry::event(*id);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
                EventLogEntry::EventWithPayload(id, p) => {
                    let (entry_a, entry_b) = LogEntry::event_with_payload(*id, *p);
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_a.raw());
                    byte_cursor += mem::size_of::<u32>();
                    le_bytes::write_u32(&mut payload[byte_cursor..], entry_b.raw());
                    byte_cursor += mem::size_of::<u32>();
                }
                EventLogEntry::TraceClock(lc) => {
                    let (entry_a, entry_b) = LogEntry::clock(*lc);
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
        let eid = arb_event_id()
            .prop_map(|id| LogEntryData::Event(id))
            .boxed();
        let eid_wp = (arb_event_id(), any::<u32>())
            .prop_map(|(id, p)| LogEntryData::EventWithPayload(id, p))
            .boxed();
        let tc = arb_logical_clock()
            .prop_map(|lc| LogEntryData::TraceClock(lc))
            .boxed();
        fc.prop_union(eid).or(eid_wp).or(tc)
    }

    pub fn arb_event_log_entry() -> impl Strategy<Value = EventLogEntry> {
        let tc = arb_logical_clock()
            .prop_map(|lc| EventLogEntry::TraceClock(lc))
            .boxed();
        let eid = arb_event_id()
            .prop_map(|id| EventLogEntry::Event(id))
            .boxed();
        let eid_wp = (arb_event_id(), any::<u32>())
            .prop_map(|(id, p)| EventLogEntry::EventWithPayload(id, p))
            .boxed();
        tc.prop_union(eid).or(eid_wp)
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
        )
            .prop_map(
                |(session_id, sequence_number, sequence_index, probe_id, data, receive_time)| {
                    ReportLogEntry {
                        session_id,
                        sequence_number,
                        sequence_index,
                        probe_id,
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
             ) -> Report {
                Report {
                    probe_id,
                    probe_clock,
                    seq_num,
                    frontier_clocks,
                    event_log,
                }
            }
    }

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
        let mut report_dest = vec![0; 512];
        let n_bytes = p1.report(&mut report_dest).unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes]).unwrap();
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
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![EventLogEntry::Event(EventId::new(1).unwrap())],
            }
        );

        let bytes_written = o_report.write_into_le_bytes(&mut report_dest[..]).unwrap();
        let i_report = Report::try_from(&report_dest[..bytes_written]).unwrap();
        assert_eq!(o_report, i_report);

        let snap = p1.produce_snapshot().unwrap();
        p2.record_event(EventId::new(2).unwrap());
        p2.merge_snapshot(&snap).unwrap();
        let n_bytes = p1.report(&mut report_dest).unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(1).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                seq_num: 1.into(),
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT),
                    EventLogEntry::TraceClock(LogicalClock {
                        id: ProbeId::new(1).unwrap(),
                        epoch: ProbeEpoch(1),
                        ticks: ProbeTicks(1),
                    })
                ],
            }
        );

        let bytes_written = o_report.write_into_le_bytes(&mut report_dest[..]).unwrap();
        let i_report = Report::try_from(&report_dest[..bytes_written]).unwrap();
        assert_eq!(o_report, i_report);

        p2.record_event_with_payload(EventId::new(8).unwrap(), 10);
        let n_bytes = p2.report(&mut report_dest).unwrap();
        let o_report = Report::try_from(&report_dest[..n_bytes]).unwrap();
        assert_eq!(
            o_report,
            Report {
                probe_id: ProbeId::new(2).unwrap(),
                probe_clock: LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                seq_num: 0.into(),
                frontier_clocks: vec![LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }],
                event_log: vec![
                    EventLogEntry::Event(EventId::new(2).unwrap()),
                    EventLogEntry::TraceClock(LogicalClock {
                        id: ProbeId::new(2).unwrap(),
                        epoch: ProbeEpoch(1),
                        ticks: ProbeTicks(1),
                    }),
                    EventLogEntry::TraceClock(LogicalClock {
                        id: ProbeId::new(1).unwrap(),
                        epoch: ProbeEpoch(0),
                        ticks: ProbeTicks(0),
                    }),
                    EventLogEntry::EventWithPayload(EventId::new(8).unwrap(), 10),
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

            const MEGABYTE: usize = 1024*1024;
            let mut bytes = vec![0u8; MEGABYTE];
            let bytes_written = report.write_into_le_bytes(&mut bytes).unwrap();
            prop_assert!(bytes_written > 0 && bytes_written <= bytes.len());

            match Report::try_from(&bytes[..bytes_written]) {
                Err(e) => prop_assert!(false, "Report::try_from(bytes) error: {:?}", e),
                Ok(r) => prop_assert_eq!(report, r),
            }
        }
    }
}
