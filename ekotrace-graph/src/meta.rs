use serde::Deserialize;

#[derive(Deserialize)]
pub struct ReportEvent {
    pub segment_id: u32,
    pub segment_index: u32,
    pub tracer_id: u32,
    pub event_id: Option<u32>,
    pub event_payload: Option<u32>,
    pub lc_tracer_id: Option<u32>,
    pub lc_clock: Option<u32>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct EventMeta {
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
        self.tags.split(";")
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct TracerMeta {
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub function: String,
    pub line: u32,
}
