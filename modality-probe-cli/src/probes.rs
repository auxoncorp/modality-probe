use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs::File;
use std::hash::Hash;
use std::path::PathBuf;

#[derive(
    Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Deserialize, Serialize,
)]
pub struct ProbeId(pub u32);

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct Probe {
    pub id: ProbeId,
    pub name: String,
    pub description: String,
    pub tags: String,
    pub file: String,
    pub line: String,
}

#[derive(Debug)]
pub struct Probes {
    pub path: PathBuf,
    pub probes: Vec<Probe>,
}

impl Probes {
    pub fn from_csv(probes_csv_file: &PathBuf) -> Self {
        let probes: Vec<Probe> = if probes_csv_file.exists() {
            let mut reader = csv::Reader::from_reader(
                File::open(probes_csv_file).expect("Can't open probes csv file"),
            );
            reader
                .deserialize()
                .map(|maybe_probe| maybe_probe.expect("Can't deserialize probe"))
                .map(|mut t: Probe| {
                    t.name = t.name.to_uppercase();
                    t
                })
                .collect()
        } else {
            vec![]
        };

        Probes {
            path: probes_csv_file.clone(),
            probes,
        }
    }

    pub fn write_csv(&self, probes_csv_file: &PathBuf) {
        let mut writer = csv::Writer::from_writer(
            File::create(probes_csv_file).expect("Can't open probes csv file"),
        );
        self.probes
            .iter()
            .for_each(|probe| writer.serialize(probe).expect("Can't serialize probe"));
        writer.flush().expect("Can't flush probes writer");
    }

    pub fn next_available_probe_id(&self) -> u32 {
        // Probe IDs start at 1
        1 + self
            .probes
            .iter()
            .map(|probe| probe.id.0)
            .max()
            .unwrap_or(0)
    }

    pub fn validate_nonzero_ids(&self) {
        self.probes.iter().for_each(|probe| {
            if probe.id.0 == 0 {
                panic!("Probes CSV contains invalid ProbeId (0) \"{}\"", probe.name);
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        if !has_unique_elements(self.probes.iter().map(|probe| probe.id)) {
            panic!("Probes CSV contains duplicate probe IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        if !has_unique_elements(self.probes.iter().map(|probe| probe.name.clone())) {
            panic!("Probes CSV contains duplicate probe names");
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
