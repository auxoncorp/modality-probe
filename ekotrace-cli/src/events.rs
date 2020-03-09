use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt;
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
    pub type_hint: String,
    pub file: String,
    pub function: String,
    pub line: String,
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
        if !has_unique_elements(self.0.iter().into_iter().map(|event| event.id)) {
            panic!("Events CSV contains duplicate event IDs");
        }
    }
}

impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Event (in-manifest)")?;
        writeln!(f, "ID: {}", self.id.0)?;
        writeln!(f, "Name: '{}'", self.name)?;
        writeln!(f, "Description: '{}'", self.description)?;
        writeln!(f, "Payload type: '{}'", self.type_hint)?;
        writeln!(f, "File: '{}'", self.file)?;
        writeln!(f, "Function: '{}'", self.function)?;
        write!(f, "Line: {}", self.line)
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
