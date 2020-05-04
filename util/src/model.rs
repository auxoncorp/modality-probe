use chrono::prelude::*;

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

/// A log event
///
/// This is the event id as used in the events.csv file, used in
/// the tracing library on each client, and transmitted in the
/// wire protocol.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub struct EventId(u32);

// TODO(pittma): Should this whole model be collapsed into a single
// library that both ekotrace and the udp collector can share?
impl EventId {
    pub fn new(id: u32) -> Self {
        EventId(id & !super::EVENT_WITH_PAYLOAD_MASK)
    }

    pub fn get_raw(self) -> u32 {
        self.0
    }
}

newtype! {
    /// The id of a tracer
    ///
    /// This is the tracer id as represented in the wire protocol.
    #[derive(Debug, Eq, PartialEq, Hash, Copy, Clone, PartialOrd, Ord)]
    pub struct TracerId(pub u32);
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
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LogEntryData {
    Event(EventId),
    EventWithPayload(EventId, u32),
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

/// A single entry in the log
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct LogEntry {
    /// The session in which this entry was made. Used to qualify the id field.
    pub session_id: SessionId,

    /// The segment to which this entry belongs
    pub segment_id: SegmentId,

    /// Where this entry occurs within the segment
    pub segment_index: u32,

    /// The tracer that supplied this entry
    pub tracer_id: TracerId,

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

    pub fn arb_event_id() -> impl Strategy<Value = EventId> {
        proptest::bits::u32::masked(crate::EVENT_WITH_PAYLOAD_MASK).prop_map(EventId::new)
    }

    pub fn arb_tracer_id() -> impl Strategy<Value = TracerId> {
        proptest::bits::u32::masked(0x7fffffff).prop_map_into()
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
            arb_segment_id(),
            arb_segment_index(),
            arb_tracer_id(),
            arb_log_entry_data(),
            arb_datetime(),
        )
            .prop_map(
                |(session_id, segment_id, segment_index, tracer_id, data, receive_time)| LogEntry {
                    session_id,
                    segment_id,
                    segment_index,
                    tracer_id,
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
