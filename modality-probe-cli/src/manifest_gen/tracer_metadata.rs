use crate::manifest_gen::source_location::SourceLocation;

/// Tracer metadata
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct TracerMetadata {
    pub name: String,
    pub location: SourceLocation,
    pub tags: Option<String>,
    pub description: Option<String>,
}

impl TracerMetadata {
    pub fn canonical_name(&self) -> String {
        self.name.to_uppercase()
    }
}
