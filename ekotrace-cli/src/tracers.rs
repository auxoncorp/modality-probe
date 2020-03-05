use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::path::PathBuf;

#[derive(
    Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Deserialize, Serialize,
)]
pub struct TracerId(pub u32);

#[derive(Debug, Eq, PartialEq, Hash, Deserialize, Serialize)]
pub struct Tracer {
    pub id: TracerId,
    pub name: String,
    pub description: String,
}

#[derive(Debug)]
pub struct Tracers(pub Vec<Tracer>);

impl Tracers {
    pub fn from_csv(tracers_csv_file: &PathBuf) -> Self {
        let tracers: Vec<Tracer> = if tracers_csv_file.exists() {
            let mut reader = csv::Reader::from_reader(
                File::open(tracers_csv_file).expect("Can't open tracers csv file"),
            );
            reader
                .deserialize()
                .map(|maybe_tracer| maybe_tracer.expect("Can't deserialize tracer"))
                .collect()
        } else {
            vec![]
        };

        Tracers(tracers)
    }

    pub fn into_csv(&self, tracers_csv_file: &PathBuf) {
        let mut writer = csv::Writer::from_writer(
            File::create(tracers_csv_file).expect("Can't open tracers csv file"),
        );
        self.0
            .iter()
            .for_each(|tracer| writer.serialize(tracer).expect("Can't serialize tracer"));
        writer.flush().expect("Can't flush tracers writer");
    }

    pub fn next_available_tracer_id(&self) -> u32 {
        // Tracer IDs start at 1
        1 + self.0.iter().map(|tracer| tracer.id.0).max().unwrap_or(0)
    }

    pub fn validate_nonzero_ids(&self) {
        self.0.iter().for_each(|tracer| {
            if tracer.id.0 == 0 {
                panic!(
                    "Tracers CSV contains invalid TracerId (0) \"{}\"",
                    tracer.name
                );
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        let mut uniq = HashSet::new();
        if !self
            .0
            .iter()
            .into_iter()
            .map(|tracer| tracer.id)
            .all(move |x| uniq.insert(x))
        {
            panic!("Tracers CSV contains duplicate tracer IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        let mut uniq = HashSet::new();
        if !self
            .0
            .iter()
            .into_iter()
            .map(|tracer| tracer.name.clone())
            .all(move |x| uniq.insert(x))
        {
            panic!("Tracers CSV contains duplicate tracer names");
        }
    }
}
