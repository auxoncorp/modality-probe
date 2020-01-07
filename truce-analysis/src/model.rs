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
    /// A log event
    ///
    /// This is event id as used in the events.csv file, used in the tracing
    /// library on each client, and transmitted in the wire protocol.
    pub struct EventId(pub u32);
}

newtype! {
    /// The id of a tracer
    ///
    /// This is the tracer id as represented in the wire protocol.
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

#[derive(Debug, Eq, PartialEq)]
pub struct Event {
    id: EventId,
    name: String,

    description: String,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Tracer {
    id: TracerId,
    name: String,
    description: String,
}

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

#[derive(Debug, Eq, PartialEq)]
pub struct LogEntry {
    pub id: LogEntryId,
    pub tracer_id: TracerId,
    pub data: LogEntryData,
    pub preceding_entry: Option<LogEntryId>,
    pub receive_time: DateTime<Utc>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct DerivedLogEdge {
    before: LogEntryId,
    after: LogEntryId,
}

#[cfg(test)]
#[allow(dead_code)]
pub mod test {
    use super::*;
    use proptest::prelude::*;

    pub fn arb_event_id() -> impl Strategy<Value = EventId> {
        proptest::bits::u32::masked(0x7fffffff).prop_map_into()
    }

    pub fn arb_tracer_id() -> impl Strategy<Value = TracerId> {
        proptest::bits::u32::masked(0x7fffffff).prop_map_into()
    }

    pub fn arb_log_entry_id() -> impl Strategy<Value = LogEntryId> {
        any::<u64>().prop_map_into()
    }

    pub fn arb_event() -> impl Strategy<Value = Event> {
        (arb_event_id(), any::<String>(), any::<String>()).prop_map(|(id, name, description)| {
            Event {
                id,
                name,
                description,
            }
        })
    }

    pub fn arb_tracer() -> impl Strategy<Value = Tracer> {
        (arb_tracer_id(), any::<String>(), any::<String>()).prop_map(|(id, name, description)| {
            Tracer {
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
            arb_log_entry_id(),
            arb_tracer_id(),
            arb_log_entry_data(),
            proptest::option::of(arb_log_entry_id()),
            arb_datetime(),
        )
            .prop_map(
                |(id, tracer_id, data, preceding_entry, receive_time)| LogEntry {
                    id,
                    tracer_id,
                    data,
                    preceding_entry,
                    receive_time,
                },
            )
    }

    pub fn arb_derived_log_edge() -> impl Strategy<Value = DerivedLogEdge> {
        (arb_log_entry_id(), arb_log_entry_id())
            .prop_map(|(before, after)| DerivedLogEdge { before, after })
    }
}
