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

    pub fn next_available_event_id(&self) -> u32 {
        // Event IDs start at 1
        1 + self
            .events
            .iter()
            .map(|event| event.id.0)
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
