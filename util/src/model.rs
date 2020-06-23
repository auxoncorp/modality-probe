use chrono::prelude::*;
use modality_probe::{EventId, ProbeId};

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
    LogicalClock(ProbeId, u32),
}

impl From<EventId> for LogEntryData {
    fn from(val: EventId) -> LogEntryData {
        LogEntryData::Event(val)
    }
}

impl From<(ProbeId, u32)> for LogEntryData {
    fn from((id, count): (ProbeId, u32)) -> LogEntryData {
        LogEntryData::LogicalClock(id, count)
    }
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
            LogEntryData::LogicalClock(_, _) => false,
        }
    }

    pub fn is_clock(&self) -> bool {
        match self.data {
            LogEntryData::Event(_) | LogEntryData::EventWithPayload(_, _) => false,
            LogEntryData::LogicalClock(_, _) => true,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct CrossSegmentLink {
    pub session_id: SessionId,
    pub before: SegmentId,
    pub after: SegmentId,
}

#[cfg(test)]
#[allow(dead_code)]
pub mod test {
    use super::*;
    use proptest::prelude::*;

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

    prop_compose! {
        pub(crate) fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
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
        let lc = (arb_probe_id(), any::<u32>()).prop_map_into().boxed();
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

    // pub fn arb_derived_log_edge() -> impl Strategy<Value = DerivedLogEdge> {
    //     (arb_session_id(), arb_log_entry_id(), arb_log_entry_id()).prop_map(
    //         |(session_id, before, after)| DerivedLogEdge {
    //             session_id,
    //             before,
    //             after,

    //     )
    // }
}
