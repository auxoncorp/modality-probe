use crate::{
    component::{ComponentHasherExt, ComponentUuId},
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
pub struct ProbeId(pub u32);

#[derive(Derivative, Clone, Debug, Deserialize, Serialize)]
#[derivative(PartialEq, Hash, PartialOrd)]
pub struct Probe {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub uuid: ComponentUuId,
    pub id: ProbeId,
    pub name: String,
    pub description: String,
    pub tags: String,
    pub file: String,
    pub line: String,
}

impl Probe {
    // Excludes UUID, description, file and line
    pub fn instrumentation_hash<H: ComponentHasherExt>(&self, state: &mut H) {
        state.update(self.id.0.to_le_bytes());
        state.update(self.name.as_bytes());
        state.update(self.tags.as_bytes());
    }
}

#[derive(Debug)]
pub struct Probes {
    pub path: PathBuf,
    pub probes: Vec<Probe>,
}

impl Probes {
    pub fn from_csv<P: AsRef<Path>>(path: P) -> Self {
        let probes: Vec<Probe> = if path.as_ref().exists() {
            let mut reader = csv::Reader::from_reader(
                File::open(&path).unwrap_or_exit("Can't open probes manifest file"),
            );
            reader
                .deserialize()
                .map(|maybe_probe| maybe_probe.unwrap_or_exit("Can't deserialize probe"))
                .map(|mut t: Probe| {
                    t.name = t.name.to_uppercase();
                    t
                })
                .collect()
        } else {
            vec![]
        };

        Probes {
            path: path.as_ref().to_path_buf(),
            probes,
        }
    }

    pub fn write_csv<P: AsRef<Path>>(&self, path: P) {
        let mut writer = csv::Writer::from_writer(
            File::create(&path).unwrap_or_exit("Can't create probes manifest file"),
        );
        self.probes.iter().for_each(|probe| {
            writer
                .serialize(probe)
                .unwrap_or_exit("Can't serialize probe")
        });
        writer.flush().unwrap_or_exit("Can't flush probes writer");
    }

    pub fn next_available_probe_id(&self) -> u32 {
        // Probe IDs are NonZeroU32, and therefore start at 1
        1 + self
            .probes
            .iter()
            .map(|probe| probe.id.0)
            .max()
            .unwrap_or(0)
    }

    pub fn validate_ids(&self) {
        self.probes.iter().for_each(|probe| {
            if modality_probe::ProbeId::new(probe.id.0).is_none() {
                exit_error!(
                    "probes",
                    "Probes manifest contains a probe \"{}\" with an invalid ProbeId ({})",
                    probe.name,
                    probe.id.0,
                );
            }
        });
    }

    pub fn validate_unique_ids(&self) {
        if !has_unique_elements(self.probes.iter().map(|probe| probe.id)) {
            exit_error!("probes", "Probes manifest contains duplicate probe IDs");
        }
    }

    pub fn validate_unique_names(&self) {
        if !has_unique_elements(self.probes.iter().map(|probe| probe.name.clone())) {
            exit_error!("probes", "Probes manifest contains duplicate probe names");
        }
    }

    pub fn instrumentation_hash<H: ComponentHasherExt>(&self, state: &mut H) {
        for p in self.probes.iter() {
            p.instrumentation_hash(state);
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
