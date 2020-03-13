use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::hash::Hash;
use std::path::PathBuf;

#[derive(
    Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Deserialize, Serialize,
)]
pub struct TracerId(pub u32);

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct Tracer {
    pub id: TracerId,
    pub name: String,
    pub description: String,
    pub file: String,
    pub function: String,
    pub line: String,
}

#[derive(Debug)]
pub struct Tracers {
    pub path: PathBuf,
    pub tracers: Vec<Tracer>,
}

impl Tracers {
    pub fn from_csv(tracers_csv_file: &PathBuf) -> Self {
        let tracers: Vec<Tracer> = if tracers_csv_file.exists() {
            let mut reader = csv::Reader::from_reader(
                File::open(tracers_csv_file).expect("Can't open tracers csv file"),
            );
            reader
                .deserialize()
                .map(|maybe_tracer| maybe_tracer.expect("Can't deserialize tracer"))
                .map(|mut t: Tracer| {
                    t.name = t.name.to_uppercase();
                    t
                })
                .collect()
        } else {
            vec![]
        };

        Tracers {
            path: tracers_csv_file.clone(),
            tracers,
        }
    }

    pub fn write_csv(&self, tracers_csv_file: &PathBuf) {
        let mut writer = csv::Writer::from_writer(
            File::create(tracers_csv_file).expect("Can't open tracers csv file"),
        );
        self.tracers
            .iter()
            .for_each(|tracer| writer.serialize(tracer).expect("Can't serialize tracer"));
        writer.flush().expect("Can't flush tracers writer");
    }

    pub fn next_available_tracer_id(&self) -> u32 {
        // Tracer IDs start at 1
        1 + self
            .tracers
            .iter()
            .map(|tracer| tracer.id.0)
            .max()
            .unwrap_or(0)
    }

    pub fn validate_nonzero_ids(&self) {
        self.tracers.iter().for_each(|tracer| {
            if tracer.id.0 == 0 {
                panic!(
                    "Tracers CSV contains invalid TracerId (0) \"{}\"",
                    tracer.name
                );
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        if !has_unique_elements(self.tracers.iter().map(|tracer| tracer.id)) {
            panic!("Tracers CSV contains duplicate tracer IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        if !has_unique_elements(self.tracers.iter().map(|tracer| tracer.name.clone())) {
            panic!("Tracers CSV contains duplicate tracer names");
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
