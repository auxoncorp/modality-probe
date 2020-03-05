use crate::manifest_gen::tracer_metadata::TracerMetadata;
use crate::tracers::TracerId;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceTracer {
    pub file: String,
    pub metadata: TracerMetadata,
}
