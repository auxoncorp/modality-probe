use crate::manifest_gen::tracer_metadata::TracerMetadata;
use crate::tracers::{Tracer, TracerId};
use std::fmt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceTracer {
    pub file: String,
    pub metadata: TracerMetadata,
}

impl InSourceTracer {
    pub fn name(&self) -> &str {
        &self.metadata.name
    }

    pub fn canonical_name(&self) -> String {
        self.metadata.canonical_name()
    }

    pub fn to_tracer(&self, id: TracerId) -> Tracer {
        Tracer {
            id,
            name: self.canonical_name(),
            description: String::new(),
            file: self.file.clone(),
            function: String::new(),
            line: self.metadata.location.line.to_string(),
        }
    }

    fn cmp_eq(&self, other: &Tracer) -> bool {
        self.canonical_name()
            .as_str()
            .eq_ignore_ascii_case(other.name.as_str())
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

impl PartialEq<Tracer> for InSourceTracer {
    fn eq(&self, other: &Tracer) -> bool {
        self.cmp_eq(other)
    }
}

impl PartialEq<&Tracer> for InSourceTracer {
    fn eq(&self, other: &&Tracer) -> bool {
        self.cmp_eq(other)
    }
}

impl fmt::Display for InSourceTracer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Tracer (in-source)")?;
        writeln!(f, "file: '{}'", self.file)?;
        write!(f, "{}", self.metadata)
    }
}
