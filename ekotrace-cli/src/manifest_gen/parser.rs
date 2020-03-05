use crate::manifest_gen::event_metadata::EventMetadata;
use crate::manifest_gen::tracer_metadata::TracerMetadata;

pub trait Parser {
    type Error;

    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, Self::Error>;

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, Self::Error>;
}
