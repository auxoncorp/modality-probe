use crate::{
    manifest_gen::{file_path::FilePath, tracer_metadata::TracerMetadata},
    tracers::{Tracer, TracerId},
};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct InSourceTracer {
    pub file: FilePath,
    pub metadata: TracerMetadata,
}

impl InSourceTracer {
    pub fn name(&self) -> &str {
        &self.metadata.name
    }

    pub fn canonical_name(&self) -> String {
        self.metadata.canonical_name()
    }

    pub fn to_tracer(&self, id: TracerId) -> Tracer {
        Tracer {
            id,
            name: self.canonical_name(),
            description: String::new(),
            file: self.file.path.clone(),
            function: String::new(),
            line: self.metadata.location.line.to_string(),
        }
    }

    fn cmp_eq(&self, other: &Tracer) -> bool {
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

impl PartialEq<Tracer> for InSourceTracer {
    fn eq(&self, other: &Tracer) -> bool {
        self.cmp_eq(other)
    }
}

impl PartialEq<&Tracer> for InSourceTracer {
    fn eq(&self, other: &&Tracer) -> bool {
        self.cmp_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality() {
        let in_src_tracer = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
            },
        };
        let in_mf_tracer = Tracer {
            id: TracerId(1),
            name: "location_a".to_string(),
            description: String::from("not in src"),
            file: "main.c".to_string(),
            function: String::new(),
            line: "4".to_string(),
        };
        assert!(in_src_tracer.eq(&in_mf_tracer));
    }
}
