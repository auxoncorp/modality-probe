use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::hash::Hash;
use std::path::PathBuf;

#[derive(
    Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Deserialize, Serialize,
)]
pub struct EventId(pub u32);

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct Event {
    pub id: EventId,
    pub name: String,
    pub description: String,
    pub tags: String,
    pub type_hint: String,
    pub file: String,
    pub line: String,
}

#[derive(Debug)]
pub struct Events {
    pub path: PathBuf,
    pub events: Vec<Event>,
}

impl Events {
    /// The events reserved for internal use
    pub fn internal_events() -> Vec<Event> {
        vec![
            Event {
                id: EventId(ekotrace::EventId::EVENT_PRODUCED_EXTERNAL_REPORT.get_raw()),
                name: "INTERNAL_EVENT_PRODUCED_EXTERNAL_REPORT".to_string(),
                description: "The tracer produced a log report for transmission to \
                    the backend for external analysis"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                id: EventId(ekotrace::EventId::EVENT_LOG_OVERFLOWED.get_raw()),
                name: "INTERNAL_EVENT_LOG_OVERFLOWED".to_string(),
                description: "There was not sufficient room in memory to store all desired events or clock data"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                id: EventId(ekotrace::EventId::EVENT_LOGICAL_CLOCK_OVERFLOWED.get_raw()),
                name: "INTERNAL_EVENT_LOGICAL_CLOCK_OVERFLOWED".to_string(),
                description: "A logical clock's count reached the maximum trackable value"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
            Event {
                id: EventId(ekotrace::EventId::EVENT_NUM_CLOCKS_OVERFLOWED.get_raw()),
                name: "INTERNAL_EVENT_NUM_CLOCKS_OVERFLOWED".to_string(),
                description: "The tracer did not have enough memory reserved to store enough logical \
                    clocks to track all of the unique neighbors that attempt to communicate with it"
                    .to_string(),
                tags: "internal".to_string(),
                type_hint: String::new(),
                file: String::new(),
                line: String::new(),
            },
        ]
    }

    pub fn from_csv(events_csv_file: &PathBuf) -> Self {
        let events: Vec<Event> = if events_csv_file.exists() {
            let mut events_reader = csv::Reader::from_reader(
                File::open(events_csv_file).expect("Can't open events csv file"),
            );
            events_reader
                .deserialize()
                .map(|maybe_event| maybe_event.expect("Can't deserialize event"))
                .map(|mut e: Event| {
                    e.name = e.name.to_uppercase();
                    e
                })
                .collect()
        } else {
            vec![]
        };

        Events {
            path: events_csv_file.clone(),
            events,
        }
    }

    pub fn write_csv(&self, events_csv_file: &PathBuf) {
        let mut events_writer = csv::Writer::from_writer(
            File::create(events_csv_file).expect("Can't open events csv file"),
        );
        self.events.iter().for_each(|event| {
            events_writer
                .serialize(event)
                .expect("Can't serialize event")
        });
        events_writer.flush().expect("Can't flush events writer");
    }

    pub fn next_available_event_id(&self, internal_events: &[u32]) -> u32 {
        // Event IDs start at 1
        1 + self
            .events
            .iter()
            .map(|event| event.id.0)
            .map(|id| if internal_events.contains(&id) { 0 } else { id })
            .max()
            .unwrap_or(0)
    }

    pub fn validate_nonzero_ids(&self) {
        self.events.iter().for_each(|event| {
            if event.id.0 == 0 {
                panic!("Events CSV contains invalid EventId (0) \"{}\"", event.name);
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        if !has_unique_elements(self.events.iter().map(|event| event.id)) {
            panic!("Events CSV contains duplicate event IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        if !has_unique_elements(self.events.iter().map(|event| event.name.clone())) {
            panic!("Events CSV contains duplicate event names");
        }
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
            ekotrace::EventId::INTERNAL_EVENTS.len()
        );
        ekotrace::EventId::INTERNAL_EVENTS
            .iter()
            .zip(internal_events.iter())
            .for_each(|(a, b)| assert_eq!(a.get_raw(), b.id.0));
    }

    #[test]
    fn next_available_id_skips_internal_ids() {
        let internal_events: Vec<u32> = ekotrace::EventId::INTERNAL_EVENTS
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
