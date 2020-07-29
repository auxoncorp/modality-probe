use crate::{
    component::{ComponentHasherExt, ComponentUuid},
    error::GracefulExit,
    exit_error,
};
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::hash::Hash;
use std::path::{Path, PathBuf};

#[derive(
    Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Deserialize, Serialize,
)]
pub struct EventId(pub u32);

#[derive(Derivative, Clone, Debug, Deserialize, Serialize)]
#[derivative(PartialEq, Hash, PartialOrd)]
pub struct Event {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub component_id: ComponentUuid,
    pub id: EventId,
    pub name: String,
    pub description: String,
    pub tags: String,
    pub type_hint: String,
    pub file: String,
    pub line: String,
}

impl Event {
    // Excludes UUID, description, file and line
    pub fn instrumentation_hash<H: ComponentHasherExt>(&self, state: &mut H) {
        state.update(self.id.0.to_le_bytes());
        state.update(self.name.as_bytes());
        state.update(self.tags.as_bytes());
        state.update(self.type_hint.as_bytes());
    }
}

#[derive(Clone, PartialEq, PartialOrd, Hash, Debug)]
pub struct Events {
    pub path: PathBuf,
    pub events: Vec<Event>,
}

impl Events {
    /// The events reserved for internal use
    pub fn internal_events() -> Vec<Event> {
        let component_id = ComponentUuid::nil();
        vec![
            Event {
                component_id,
                id: EventId(modality_probe::EventId::EVENT_PRODUCED_EXTERNAL_REPORT.get_raw()),
                name: "INTERNAL_EVENT_PRODUCED_EXTERNAL_REPORT".to_string(),
                description: "The probe produced a log report for transmission to \
                    the backend for external analysis"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                component_id,
                id: EventId(modality_probe::EventId::EVENT_LOG_ITEMS_MISSED.get_raw()),
                name: "INTERNAL_EVENT_LOG_ITEMS_MISSED".to_string(),
                description: "n log items were overwritten without successfully getting \
                    reported to the collector, where n is the payload"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                component_id,
                id: EventId(modality_probe::EventId::EVENT_LOGICAL_CLOCK_OVERFLOWED.get_raw()),
                name: "INTERNAL_EVENT_LOGICAL_CLOCK_OVERFLOWED".to_string(),
                description: "A logical clock's count reached the maximum trackable value"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                component_id,
                id: EventId(modality_probe::EventId::EVENT_NUM_CLOCKS_OVERFLOWED.get_raw()),
                name: "INTERNAL_EVENT_NUM_CLOCKS_OVERFLOWED".to_string(),
                description:
                    "The probe did not have enough memory reserved to store enough logical \
                    clocks to track all of the unique neighbors that attempt to communicate with it"
                        .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
        ]
    }

    pub fn from_csv<P: AsRef<Path>>(path: P) -> Self {
        let events: Vec<Event> = if path.as_ref().exists() {
            let mut events_reader = csv::Reader::from_reader(
                File::open(&path).unwrap_or_exit("Can't open events manifest file"),
            );
            events_reader
                .deserialize()
                .map(|maybe_event| maybe_event.unwrap_or_exit("Can't deserialize event"))
                .map(|mut e: Event| {
                    e.name = e.name.to_uppercase();
                    e
                })
                .collect()
        } else {
            vec![]
        };

        Events {
            path: path.as_ref().to_path_buf(),
            events,
        }
    }

    pub fn write_csv<P: AsRef<Path>>(&self, path: P) {
        let mut events_writer = csv::Writer::from_writer(
            File::create(&path).unwrap_or_exit("Can't create events manifest file"),
        );
        self.events.iter().for_each(|event| {
            events_writer
                .serialize(event)
                .unwrap_or_exit("Can't serialize event")
        });
        events_writer
            .flush()
            .unwrap_or_exit("Can't flush events writer");
    }

    pub fn next_available_event_id(&self, internal_events: &[u32]) -> u32 {
        // Event IDs are NonZeroU32, and therefor start at 1
        1 + self
            .events
            .iter()
            .map(|event| event.id.0)
            .map(|id| if internal_events.contains(&id) { 0 } else { id })
            .max()
            .unwrap_or(0)
    }

    pub fn validate_ids(&self) {
        self.events.iter().for_each(|event| {
            let is_valid_user_id = modality_probe::EventId::new(event.id.0).is_some();
            let is_valid_internal_id = modality_probe::EventId::new_internal(event.id.0).is_some();

            if is_valid_internal_id && !event.tags.contains("internal") {
                exit_error!(
                    "events",
                    "Events manifest contains an event \"{}\" with an EventId ({}) in the internal range but is missing the \"internal\" tag",
                    event.name,
                    event.id.0,
                );
            }

            if !is_valid_user_id && !is_valid_internal_id {
                exit_error!(
                    "events",
                    "Events manifest contains an event \"{}\" with an invalid EventId ({})",
                    event.name,
                    event.id.0,
                );
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        if !has_unique_elements(self.events.iter().map(|event| event.id)) {
            exit_error!("events", "Events manifest contains duplicate event IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        if !has_unique_elements(self.events.iter().map(|event| event.name.clone())) {
            exit_error!("events", "Events manifest contains duplicate event names");
        }
    }

    pub fn instrumentation_hash<H: ComponentHasherExt>(&self, state: &mut H) {
        for e in self.events.iter() {
            e.instrumentation_hash(state);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Event> {
        self.events.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Event> {
        self.events.iter_mut()
    }
}

fn has_unique_elements<T>(iter: T) -> bool
where
    T: IntoIterator,
    T::Item: Eq + Hash,
{
    let mut uniq = HashSet::new();
    iter.into_iter().all(move |x| uniq.insert(x))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn internal_events() {
        let internal_events = Events::internal_events();
        assert_eq!(
            internal_events.len(),
            modality_probe::EventId::INTERNAL_EVENTS.len()
        );
        modality_probe::EventId::INTERNAL_EVENTS
            .iter()
            .zip(internal_events.iter())
            .for_each(|(a, b)| assert_eq!(a.get_raw(), b.id.0));
    }

    #[test]
    fn next_available_id_skips_internal_ids() {
        let internal_events: Vec<u32> = modality_probe::EventId::INTERNAL_EVENTS
            .iter()
            .map(|id| id.get_raw())
            .collect();
        let e = Events {
            path: PathBuf::from("."),
            events: Events::internal_events(),
        };
        assert_eq!(e.next_available_event_id(&internal_events), 1);
    }
}
