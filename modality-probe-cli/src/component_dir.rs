use crate::{component::Component, events::Events, exit_error, probes::Probes};
use std::collections::HashSet;
use std::hash::Hash;
use std::path::{Path, PathBuf};
use walkdir::{DirEntry, WalkDir};

#[derive(Clone, PartialEq, PartialOrd, Hash, Debug)]
pub struct ComponentDir {
    pub directory: PathBuf,
    pub component: Component,
    pub probes: Probes,
    pub events: Events,
}

impl ComponentDir {
    pub fn component_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("Component.toml")
    }

    pub fn probes_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("probes.csv")
    }

    pub fn events_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("events.csv")
    }

    pub fn from_path_parts<P: AsRef<Path>>(
        component_directory: P,
        component_path: P,
        probes_path: P,
        events_path: P,
    ) -> Self {
        ComponentDir {
            directory: component_directory.as_ref().to_path_buf(),
            component: Component::from_toml(component_path),
            probes: Probes::from_csv(probes_path),
            events: Events::from_csv(events_path),
        }
    }

    pub fn collect_from_path<P: AsRef<Path>>(path: P) -> Vec<Self> {
        let mut comp_dirs = Vec::new();
        for entry in WalkDir::new(&path)
            .sort_by(|a, b| a.file_name().cmp(b.file_name()))
            .into_iter()
            .filter_entry(|e| !is_hidden(e))
            .filter_map(Result::ok)
            .filter(|e| e.file_type().is_dir())
        {
            let component_directory = entry.path().to_path_buf();
            let component_manifest_path = Self::component_manifest_path(&component_directory);
            let probes_manifest_path = Self::probes_manifest_path(&component_directory);
            let events_manifest_path = Self::events_manifest_path(&component_directory);

            if component_manifest_path.exists() {
                comp_dirs.push(ComponentDir::from_path_parts(
                    component_directory,
                    component_manifest_path,
                    probes_manifest_path,
                    events_manifest_path,
                ))
            }
        }

        for c in comp_dirs.iter() {
            if c.component.name.is_empty() {
                exit_error!(
                    "components",
                    "Found a component with an empty name field at {}",
                    Self::component_manifest_path(&c.directory).display()
                );
            }
        }

        if !has_unique_elements(comp_dirs.iter().map(|c| c.component.name.clone())) {
            exit_error!(
                "components",
                "Components directory contains duplicate components with the same name"
            );
        }

        comp_dirs
    }

    pub fn write_manifest_files(&self) {
        let component_manifest_path = Self::component_manifest_path(&self.directory);
        let probes_manifest_path = Self::probes_manifest_path(&self.directory);
        let events_manifest_path = Self::events_manifest_path(&self.directory);

        self.component.write_toml(&component_manifest_path);
        self.probes.write_csv(&probes_manifest_path);
        self.events.write_csv(&events_manifest_path);
    }
}

fn is_hidden(entry: &DirEntry) -> bool {
    entry
        .file_name()
        .to_str()
        .map(|s| s.starts_with('.') && s != "." && s != "./")
        .unwrap_or(false)
}

fn has_unique_elements<T>(iter: T) -> bool
where
    T: IntoIterator,
    T::Item: Eq + Hash,
{
    let mut uniq = HashSet::new();
    iter.into_iter().all(move |x| uniq.insert(x))
}
