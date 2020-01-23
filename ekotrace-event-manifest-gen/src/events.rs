use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::path::PathBuf;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub struct EventId(pub u32);

#[derive(Debug, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub struct Event {
    pub id: EventId,
    pub name: String,
    pub description: String,
}

#[derive(Debug)]
pub struct Events(pub Vec<Event>);

impl Events {
    pub fn from_csv(events_csv_file: &PathBuf) -> Self {
        let events: Vec<Event> = if events_csv_file.exists() {
            let mut events_reader = csv::Reader::from_reader(
                File::open(events_csv_file).expect("Can't open events csv file"),
            );
            events_reader
                .deserialize()
                .map(|maybe_event| maybe_event.expect("Can't deserialize event"))
                .collect()
        } else {
            vec![]
        };

        Events(events)
    }

    pub fn into_csv(&self, events_csv_file: &PathBuf) {
        let mut events_writer = csv::Writer::from_writer(
            File::create(events_csv_file).expect("Can't open events csv file"),
        );
        self.0.iter().for_each(|event| {
            events_writer
                .serialize(event)
                .expect("Can't serialize event")
        });
        events_writer.flush().expect("Can't flush events writer");
    }

    pub fn next_available_event_id(&self) -> u32 {
        // Event IDs start at 1
        1 + self.0.iter().map(|event| event.id.0).max().unwrap_or(0)
    }

    pub fn validate_nonzero_ids(&self) {
        self.0.iter().for_each(|event| {
            if event.id.0 == 0 {
                panic!("Events CSV contains invalid EventId (0) \"{}\"", event.name);
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        let mut uniq = HashSet::new();
        if !self
            .0
            .iter()
            .into_iter()
            .map(|event| event.id)
            .all(move |x| uniq.insert(x))
        {
            panic!("Events CSV contains duplicate event IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        let mut uniq = HashSet::new();
        if !self
            .0
            .iter()
            .into_iter()
            .map(|event| event.name.clone())
            .all(move |x| uniq.insert(x))
        {
            panic!("Events CSV contains duplicate event names");
        }
    }
}
