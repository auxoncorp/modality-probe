use crate::{
    events::{Event, EventId},
    manifest_gen::{event_metadata::EventMetadata, file_path::FilePath},
};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceEvent {
    pub file: FilePath,
    pub metadata: EventMetadata,
}

impl InSourceEvent {
    pub fn name(&self) -> &str {
        &self.metadata.name
    }

    pub fn canonical_name(&self) -> String {
        self.metadata.canonical_name()
    }

    pub fn to_event(&self, id: EventId) -> Event {
        Event {
            id,
            name: self.canonical_name(),
            description: self
                .metadata
                .description
                .as_ref()
                .map_or(String::new(), |s| s.clone()),
            type_hint: self
                .metadata
                .payload
                .as_ref()
                .map_or(String::new(), |p| p.0.to_string()),
            file: self.file.path.clone(),
            function: String::new(),
            line: self.metadata.location.line.to_string(),
        }
    }

    pub fn cmp_eq(&self, other: &Event) -> bool {
        self.canonical_name()
            .as_str()
            .eq_ignore_ascii_case(other.name.as_str())
            && self
                .metadata
                .payload
                .as_ref()
                .map_or("", |p| p.0.as_str())
                .eq_ignore_ascii_case(other.type_hint.as_str())
            && self.file.path.as_str().eq(other.file.as_str())
            && self
                .metadata
                .location
                .line
                .to_string()
                .as_str()
                .eq_ignore_ascii_case(other.line.as_str())
    }
}

impl PartialEq<Event> for InSourceEvent {
    fn eq(&self, other: &Event) -> bool {
        self.cmp_eq(other)
    }
}

impl PartialEq<&Event> for InSourceEvent {
    fn eq(&self, other: &&Event) -> bool {
        self.cmp_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest_gen::type_hint::TypeHint;

    #[test]
    fn equality() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: Some((TypeHint::U8, "mydata").into()),
                description: None,
                location: (1, 2, 3).into(),
            },
        };

        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::from("stuff not in the src"),
            type_hint: String::from("u8"),
            file: "main.c".to_string(),
            function: String::new(),
            line: "2".to_string(),
        };
        assert!(in_src_event.eq(&in_mf_event));
    }
}
