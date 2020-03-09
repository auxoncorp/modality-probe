use crate::manifest_gen::source_location::SourceLocation;
use std::fmt;

/// Tracer metadata
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct TracerMetadata {
    pub name: String,
    pub location: SourceLocation,
}

impl TracerMetadata {
    pub fn canonical_name(&self) -> String {
        self.name.to_lowercase()
    }
}

impl fmt::Display for TracerMetadata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Name: '{}'", self.canonical_name())?;
        write!(f, "{}", self.location)
    }
}
