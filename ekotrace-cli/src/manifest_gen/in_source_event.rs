use crate::events::{Event, EventId};
use crate::manifest_gen::event_metadata::EventMetadata;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceEvent {
    pub file: String,
    pub metadata: EventMetadata,
}

impl InSourceEvent {
    pub fn to_event(&self, id: EventId) -> Event {
        Event {
            id,
            name: self.metadata.name.clone(),
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
    fn eq(&self, other: &&Event) -> bool {
        self.metadata
            .name
            .as_str()
            .eq_ignore_ascii_case(other.name.as_str())
            && self
                .metadata
                .payload
                .as_ref()
                .map_or("", |p| p.0.as_str())
                .eq_ignore_ascii_case(other.type_hint.as_str())
            && self.file.as_str().eq_ignore_ascii_case(other.file.as_str())
            && self
                .metadata
                .location
                .line
                .to_string()
                .as_str()
                .eq_ignore_ascii_case(other.line.as_str())
    }
}
