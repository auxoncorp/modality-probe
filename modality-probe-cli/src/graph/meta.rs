//! The ser/de types for report events and event and probe metadata.
use serde::Deserialize;
use uuid::Uuid;

/// A row in the columnar report collection.
#[derive(Debug, Clone, Deserialize)]
pub struct ReportEvent {
    pub segment_id: u32,
    pub segment_index: u32,
    pub probe_id: u32,
    pub event_id: Option<u32>,
    pub event_payload: Option<u32>,
    pub lc_probe_id: Option<u32>,
    pub lc_clock: Option<u32>,
}

/// A row in the events.csv for a component.
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub struct EventMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub type_hint: Option<String>,
    pub tags: String,
    pub description: String,
    pub file: String,
    pub line: Option<u32>,
}

impl EventMeta {
    pub fn tags_iter(&self) -> impl Iterator<Item = &str> {
        self.tags.split(';')
    }
}

/// A row in probes.csv for a component.
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub struct ProbeMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub line: u32,
}
