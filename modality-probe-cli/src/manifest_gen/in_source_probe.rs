use crate::{
    manifest_gen::{file_path::FilePath, probe_metadata::ProbeMetadata},
    probes::{Probe, ProbeId},
};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceProbe {
    pub file: FilePath,
    pub metadata: ProbeMetadata,
}

impl InSourceProbe {
    pub fn name(&self) -> &str {
        &self.metadata.name
    }

    pub fn canonical_name(&self) -> String {
        self.metadata.canonical_name()
    }

    pub fn to_probe(&self, id: ProbeId) -> Probe {
        Probe {
            id,
            name: self.canonical_name(),
            description: self
                .metadata
                .description
                .as_ref()
                .map_or(String::new(), |s| s.clone()),
            tags: self
                .metadata
                .tags
                .as_ref()
                .map_or(String::new(), |s| s.clone()),
            file: self.file.path.clone(),
            line: self.metadata.location.line.to_string(),
        }
    }

    fn cmp_eq(&self, other: &Probe) -> bool {
        self.canonical_name()
            .as_str()
            .eq_ignore_ascii_case(other.name.as_str())
            && self
                .file
                .path
                .as_str()
                .eq_ignore_ascii_case(other.file.as_str())
            && self
                .metadata
                .location
                .line
                .to_string()
                .as_str()
                .eq_ignore_ascii_case(other.line.as_str())
    }
}

impl PartialEq<Probe> for InSourceProbe {
    fn eq(&self, other: &Probe) -> bool {
        self.cmp_eq(other)
    }
}

impl PartialEq<&Probe> for InSourceProbe {
    fn eq(&self, other: &&Probe) -> bool {
        self.cmp_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality() {
        let in_src_probe = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "PROBE_ID_A".to_string(),
                location: (1, 4, 3).into(),
                tags: None,
                description: None,
            },
        };
        let in_mf_probe = Probe {
            id: ProbeId(1),
            name: "PROBE_ID_A".to_string(),
            description: String::from("not in src"),
            tags: String::new(),
            file: "main.c".to_string(),
            line: "4".to_string(),
        };
        assert!(in_src_probe.eq(&in_mf_probe));
    }
}
