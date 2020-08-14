//! The ser/de types for report events and event and probe metadata.
use serde::Deserialize;
use uuid::Uuid;

/// A row in the events.csv for a component.
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub(crate) struct EventMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub type_hint: Option<String>,
    pub tags: String,
    pub description: String,
    pub file: String,
    pub line: u32,
}

/// A row in probes.csv for a component.
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub(crate) struct ProbeMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub line: u32,
}
