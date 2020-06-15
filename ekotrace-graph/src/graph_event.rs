//! This module contains the node types that are used by the graph
//! builders.

/// The type used by event-based builders.
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum GraphEvent<'a> {
    Event {
        name: &'a str,
        location: &'a str,
        clock: u32,
        clock_offset: u32,
    },
    WithPayload {
        name: &'a str,
        location: &'a str,
        clock: u32,
        clock_offset: u32,
        payload: u32,
    },
}

impl<'a> GraphEvent<'a> {
    /// Get the event's name.
    pub fn name(&self) -> &'a str {
        match self {
            GraphEvent::Event { name, .. } => name,
            GraphEvent::WithPayload { name, .. } => name,
        }
    }

    /// Get the event's location.
    pub fn location(&self) -> &'a str {
        match self {
            GraphEvent::Event { location, .. } => location,
            GraphEvent::WithPayload { location, .. } => location,
        }
    }

    /// Get the event's clock value.
    pub fn clock(&self) -> u32 {
        match self {
            GraphEvent::Event { clock, .. } => *clock,
            GraphEvent::WithPayload { clock, .. } => *clock,
        }
    }

    /// Get the event's clock offset, also knows as "segment index".
    pub fn clock_offset(&self) -> u32 {
        match self {
            GraphEvent::Event { clock_offset, .. } => *clock_offset,
            GraphEvent::WithPayload { clock_offset, .. } => *clock_offset,
        }
    }

    /// Use the type hint from this event and stringify the payload
    /// through the type hint.
    ///
    /// This is to provide a way to get at the payload information
    /// when generating the textual form of a graph.
    pub fn parsed_payload(&self, type_hint: &str) -> Option<String> {
        match self {
            GraphEvent::Event { .. } => None,
            GraphEvent::WithPayload { payload, .. } => match type_hint {
                "i8" => Some(format!("{}", *payload as i8)),
                "i16" => Some(format!("{}", *payload as i16)),
                "i32" => Some(format!("{}", *payload as i32)),
                "u8" => Some(format!("{}", *payload as u8)),
                "u16" => Some(format!("{}", *payload as u16)),
                "u32" => Some(format!("{}", *payload as u32)),
                "f32" => Some(format!("{}", *payload as f32)),
                "bool" => Some(format!("{}", *payload != 0)),
                _ => None,
            },
        }
    }
}

/// The node type used for segment based graphs.
#[derive(PartialEq, Eq, Clone, Copy, Hash, Default)]
pub struct GraphSegment<'a> {
    pub name: &'a str,
    pub clock: u32,
}
