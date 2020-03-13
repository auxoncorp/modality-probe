use crate::manifest_gen::source_location::SourceLocation;
use crate::manifest_gen::type_hint::TypeHint;

/// Event payload type hint and token
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Payload(pub TypeHint, pub String);

/// Event metadata
///
/// Events with payloads will have a `payload` field.
/// Events that have already been assigned an identifier will
/// have `assigned_id` set.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct EventMetadata {
    pub name: String,
    pub ekotrace_instance: String,
    pub payload: Option<Payload>,
    pub description: Option<String>,
    pub location: SourceLocation,
}

impl EventMetadata {
    pub fn canonical_name(&self) -> String {
        self.name.to_uppercase()
    }
}

impl From<(TypeHint, String)> for Payload {
    fn from(triple: (TypeHint, String)) -> Payload {
        Payload(triple.0, triple.1)
    }
}

impl From<(TypeHint, &str)> for Payload {
    fn from(triple: (TypeHint, &str)) -> Payload {
        Payload(triple.0, triple.1.to_string())
    }
}
