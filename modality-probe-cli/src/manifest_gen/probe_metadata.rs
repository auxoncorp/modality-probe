use crate::manifest_gen::source_location::SourceLocation;

/// Probe metadata
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct ProbeMetadata {
    pub name: String,
    pub component: String,
    pub location: SourceLocation,
    pub tags: Option<String>,
    pub description: Option<String>,
}

impl ProbeMetadata {
    pub fn canonical_name(&self) -> String {
        self.name.to_uppercase()
    }

    pub fn canonical_component_name(&self) -> String {
        self.component.to_lowercase().replace("_", "-")
    }
}
