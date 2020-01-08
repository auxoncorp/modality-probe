use chrono::prelude::*;

macro_rules! newtype {
   ($(#[$meta:meta])* pub struct $name:ident(pub $t:ty);) => {
        #[derive(Debug, Eq, PartialEq)]
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
    #[derive(Clone, Copy)]
    pub struct SessionId(pub u32);
}

newtype! {
    /// A log event
    ///
    /// This is event id as used in the events.csv file, used in the tracing
    /// library on each client, and transmitted in the wire protocol.
    #[derive(Clone, Copy)]
    pub struct EventId(pub u32);
}

newtype! {
    /// The id of a tracer
    ///
    /// This is the tracer id as represented in the wire protocol.
    #[derive(Clone, Copy)]
    pub struct TracerId(pub u32);
}

newtype! {
    /// The id of a single entry in the log
    ///
    /// This identifies a single entry in the event log, which may either be an
    /// event or a piece of a logical clock. These ids are unique within a
    /// session. It is used to represent known orderings between events.
    pub struct LogEntryId(pub u64);
}

/// Map an event id to its name and description
#[derive(Debug, Eq, PartialEq)]
pub struct EventMapping {
    id: EventId,
    name: String,
    description: String,
}

/// Map an tracer id to its name and description
#[derive(Debug, Eq, PartialEq)]
pub struct TracerMapping {
    id: TracerId,
    name: String,
    description: String,
}

/// The data that may be attached to a log entry
#[derive(Debug, Eq, PartialEq)]
pub enum LogEntryData {
    Event(EventId),
    LogicalClock(TracerId, u32),
}

impl From<EventId> for LogEntryData {
    fn from(val: EventId) -> LogEntryData {
        LogEntryData::Event(val)
    }
}

impl From<(TracerId, u32)> for LogEntryData {
    fn from((id, count): (TracerId, u32)) -> LogEntryData {
        LogEntryData::LogicalClock(id, count)
    }
}

impl From<(u32, u32)> for LogEntryData {
    fn from((id, count): (u32, u32)) -> LogEntryData {
        LogEntryData::LogicalClock(id.into(), count)
    }
}

/// A single entry in the log
#[derive(Debug, Eq, PartialEq)]
pub struct LogEntry {
    /// The session in which this entry was made. Used to qualify the id field.
    pub session_id: SessionId,

    /// The id of this entry. Unique with in the session given by session_id.
    pub id: LogEntryId,

    /// The tracer that supplied this entry
    pub tracer_id: TracerId,

    /// This entry's data; an event, or a logical clock snapshot
    pub data: LogEntryData,

    /// The entry which immediately precedes this one in the log.
    ///
    /// The preceding entry must be in the same session as this one, and should
    /// have the same tracer id. If there is no immediate predecessor available
    /// when the entry is written, None should be used. If the data is well-formed,
    /// None should only be used for LogicalClock entries.
    pub preceding_entry: Option<LogEntryId>,

    /// The time this entry was received by the collector
    ///
    /// This is the collector's system clock at the time the entry data was
    /// received, not when it was created. It is stored for convenience only;
    /// the logical clock should be used for ordering messages.
    pub receive_time: DateTime<Utc>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct DerivedLogEdge {
    pub session_id: SessionId,
    pub before: LogEntryId,
    pub after: LogEntryId,
}

#[cfg(test)]
#[allow(dead_code)]
pub mod test {
    use super::*;
    use proptest::prelude::*;

    pub fn arb_session_id() -> impl Strategy<Value = SessionId> {
        any::<u32>().prop_map_into()
    }

    pub fn arb_event_id() -> impl Strategy<Value = EventId> {
        proptest::bits::u32::masked(0x7fffffff).prop_map_into()
    }

    pub fn arb_tracer_id() -> impl Strategy<Value = TracerId> {
        proptest::bits::u32::masked(0x7fffffff).prop_map_into()
    }

    pub fn arb_log_entry_id() -> impl Strategy<Value = LogEntryId> {
        any::<u64>().prop_map_into()
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

    pub fn arb_tracer_mapping() -> impl Strategy<Value = TracerMapping> {
        (arb_tracer_id(), any::<String>(), any::<String>()).prop_map(|(id, name, description)| {
            TracerMapping {
                id,
                name,
                description,
            }
        })
    }

    pub fn arb_log_entry_data() -> impl Strategy<Value = LogEntryData> {
        let eid = arb_event_id().prop_map_into().boxed();
        let lc = (arb_tracer_id(), any::<u32>()).prop_map_into().boxed();
        eid.prop_union(lc)
    }

    pub fn arb_datetime() -> impl Strategy<Value = DateTime<Utc>> {
        any::<i64>().prop_map(|n| Utc.timestamp_nanos(n))
    }

    pub fn arb_log_entry() -> impl Strategy<Value = LogEntry> {
        (
            arb_session_id(),
            arb_log_entry_id(),
            arb_tracer_id(),
            arb_log_entry_data(),
            proptest::option::of(arb_log_entry_id()),
            arb_datetime(),
        )
            .prop_map(
                |(session_id, id, tracer_id, data, preceding_entry, receive_time)| LogEntry {
                    session_id,
                    id,
                    tracer_id,
                    data,
                    preceding_entry,
                    receive_time,
                },
            )
    }

    pub fn arb_derived_log_edge() -> impl Strategy<Value = DerivedLogEdge> {
        (arb_session_id(), arb_log_entry_id(), arb_log_entry_id()).prop_map(
            |(session_id, before, after)| DerivedLogEdge {
                session_id,
                before,
                after,
            },
        )
    }
}
