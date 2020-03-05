use crate::manifest_gen::tracer_metadata::TracerMetadata;
use crate::tracers::{Tracer, TracerId};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceTracer {
    pub file: String,
    pub metadata: TracerMetadata,
}

impl InSourceTracer {
    pub fn to_tracer(&self, id: TracerId) -> Tracer {
        Tracer {
            id,
            name: self.metadata.name.to_lowercase(),
            description: String::new(),
            file: self.file.clone(),
            function: String::new(),
            line: self.metadata.location.line.to_string(),
        }
    }
}
