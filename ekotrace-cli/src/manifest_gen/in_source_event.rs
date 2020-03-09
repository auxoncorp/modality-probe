use crate::events::{Event, EventId};
use crate::manifest_gen::event_metadata::EventMetadata;
use std::fmt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceEvent {
    pub file: String,
    pub metadata: EventMetadata,
}

impl InSourceEvent {
    pub fn canonical_name(&self) -> String {
        self.metadata.canonical_name()
    }

    pub fn id(&self) -> Option<EventId> {
        self.metadata.assigned_id.map(|id| EventId(id))
    }

    pub fn is_assigned(&self) -> bool {
        self.metadata.assigned_id.is_some()
    }

    pub fn to_event(&self, id: EventId) -> Event {
        Event {
            id,
            name: self.canonical_name(),
            description: String::new(),
            type_hint: self
                .metadata
                .payload
                .as_ref()
                .map_or(String::new(), |p| p.0.to_string()),
            file: self.file.clone(),
            function: String::new(),
            line: self.metadata.location.line.to_string(),
        }
    }
}

impl PartialEq<&Event> for InSourceEvent {
    // Ignores ID and description
    fn eq(&self, other: &&Event) -> bool {
        self.canonical_name()
            .as_str()
            .eq_ignore_ascii_case(other.name.as_str())
            && self
                .metadata
                .payload
                .as_ref()
                .map_or("", |p| p.0.as_str())
                .eq_ignore_ascii_case(other.type_hint.as_str())
            && self.file.as_str().eq(other.file.as_str())
            && self
                .metadata
                .location
                .line
                .to_string()
                .as_str()
                .eq_ignore_ascii_case(other.line.as_str())
    }
}

impl fmt::Display for InSourceEvent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Event (in-source)")?;
        writeln!(f, "file: '{}'", self.file)?;
        write!(f, "{}", self.metadata)
    }
}
