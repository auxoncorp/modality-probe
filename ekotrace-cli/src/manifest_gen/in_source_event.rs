use crate::events::EventId;
use crate::manifest_gen::event_metadata::EventMetadata;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceEvent {
    pub file: String,
    pub metadata: EventMetadata,
}
