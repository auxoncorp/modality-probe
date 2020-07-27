use crate::manifest_gen::{
    c_parser::CParser,
    file_path::{self, FilePath},
    id_gen::IdGen,
    in_source_event::InSourceEvent,
    in_source_probe::InSourceProbe,
    parser::{self, Parser},
    rust_parser::RustParser,
};
use crate::{
    component::{ComponentHash, ComponentHasher, ComponentHasherExt},
    events::{Event, EventId, Events},
    exit_error,
    lang::Lang,
    probes::{ProbeId, Probes},
    warn,
};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;
use std::fs::File;
use std::hash::Hash;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use walkdir::{DirEntry, WalkDir};

#[derive(Debug)]
pub enum CreationError {
    Io(PathBuf, io::Error),
    Parser(String, parser::Error),
    FileDoesNotExist(PathBuf),
    NotRegularFile(PathBuf),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ProbeCheckError {
    MultipleLocationsInSource(InSourceProbe, InSourceProbe),
    NameNotUpperCase(InSourceProbe),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum EventCheckError {
    DuplicateNameInSource(InSourceEvent, InSourceEvent),
    NameNotUpperCase(InSourceEvent),
}

pub struct Invocations {
    internal_events: Vec<Event>,
    probes: Vec<InSourceProbe>,
    events: Vec<InSourceEvent>,
    code_hash: ComponentHash,
}

impl Default for Invocations {
    fn default() -> Self {
        let config = Config::default();
        Invocations {
            internal_events: config.internal_events,
            probes: Default::default(),
            events: Default::default(),
            code_hash: ComponentHash([0; 32]),
        }
    }
}

pub struct Config<'cfg> {
    pub lang: Option<Lang>,
    pub c_parser: CParser<'cfg>,
    pub rust_parser: RustParser<'cfg>,
    pub file_extensions: Option<Vec<String>>,
    pub internal_events: Vec<Event>,
}

impl<'cfg> Default for Config<'cfg> {
    fn default() -> Self {
        Config {
            lang: None,
            c_parser: CParser::default(),
            rust_parser: RustParser::default(),
            file_extensions: None,
            internal_events: Events::internal_events(),
        }
    }
}

impl Invocations {
    pub fn from_path<P: AsRef<Path>>(config: Config<'_>, p: P) -> Result<Self, CreationError> {
        let mut probes = Vec::new();
        let mut events = Vec::new();
        let mut buffer = String::new();
        let mut code_hasher = ComponentHasher::new();
        for entry in WalkDir::new(&p)
            .sort_by(|a, b| a.file_name().cmp(b.file_name()))
            .into_iter()
            .filter_entry(|e| !is_hidden(e))
            .filter_map(Result::ok)
            .filter(|e| !e.file_type().is_dir())
        {
            let should_consider = config.file_extensions.as_ref().map_or(true, |exts| {
                exts.iter()
                    .any(|ext| Some(OsStr::new(ext)) == entry.path().extension())
            });
            if should_consider {
                let mut f = File::open(entry.path())
                    .map_err(|e| CreationError::Io(entry.path().to_path_buf(), e))?;

                // Skips binary/invalid data
                buffer.clear();
                if f.read_to_string(&mut buffer).is_ok() {
                    if !entry.path().exists() {
                        return Err(CreationError::FileDoesNotExist(entry.path().to_path_buf()));
                    }

                    if !entry.path().is_file() {
                        return Err(CreationError::NotRegularFile(entry.path().to_path_buf()));
                    }

                    let search_path = p
                        .as_ref()
                        .canonicalize()
                        .map_err(|e| CreationError::Io(p.as_ref().to_path_buf(), e))?;
                    let file = entry
                        .path()
                        .canonicalize()
                        .map_err(|e| CreationError::Io(entry.path().to_path_buf(), e))?;
                    let file_path = FilePath::from_path_file(&search_path, &file)?;

                    let parser: Box<dyn Parser> = match config.lang {
                        Some(Lang::C) => Box::new(config.c_parser),
                        Some(Lang::Rust) => Box::new(config.rust_parser),
                        None => match entry.path().extension() {
                            Some(os_str) => match os_str.to_str() {
                                Some("rs") => Box::new(config.rust_parser),
                                Some("c") => Box::new(config.c_parser),
                                Some(ext) => {
                                    warn!(
                                        "manifest-gen",
                                        "Guessing C parser based on file extension '{}'", ext
                                    );
                                    Box::new(config.c_parser)
                                }
                                None => {
                                    warn!(
                                        "manifest-gen",
                                        "Guessing C parser based on file extension '{}'",
                                        os_str.to_string_lossy()
                                    );
                                    Box::new(config.c_parser)
                                }
                            },
                            None => {
                                warn!(
                                    "manifest-gen",
                                    "No file extension available, defaulting to using the C parser\n\
                                    {:?}",
                                    entry.path()
                                );
                                Box::new(config.c_parser)
                            }
                        },
                    };

                    code_hasher.update(buffer.as_bytes());

                    let probe_metadata = parser
                        .parse_probes(&buffer)
                        .map_err(|e| CreationError::Parser(file_path.path.clone(), e))?;
                    let mut probes_in_file: Vec<InSourceProbe> = probe_metadata
                        .into_iter()
                        .map(|md| InSourceProbe {
                            file: file_path.clone(),
                            metadata: md,
                        })
                        .collect();
                    probes.append(&mut probes_in_file);

                    let event_metadata = parser
                        .parse_events(&buffer)
                        .map_err(|e| CreationError::Parser(file_path.path.clone(), e))?;
                    let mut events_in_file: Vec<InSourceEvent> = event_metadata
                        .into_iter()
                        .map(|md| InSourceEvent {
                            file: file_path.clone(),
                            metadata: md,
                        })
                        .collect();
                    events.append(&mut events_in_file);
                }
            }
        }

        let code_hash_bytes: [u8; 32] = *(code_hasher.finalize().as_ref());
        Ok(Invocations {
            internal_events: config.internal_events,
            probes,
            events,
            code_hash: code_hash_bytes.into(),
        })
    }

    pub fn code_hash(&self) -> ComponentHash {
        self.code_hash
    }

    pub fn check_probes(&self) -> Result<(), ProbeCheckError> {
        let mut uniq = HashMap::new();
        for t in self.probes.iter() {
            if let Some(prev_t) = uniq.insert(t.canonical_name(), t) {
                return Err(ProbeCheckError::MultipleLocationsInSource(
                    prev_t.clone(),
                    t.clone(),
                ));
            }
        }

        for t in self.probes.iter() {
            if t.name().to_uppercase() != t.name() {
                return Err(ProbeCheckError::NameNotUpperCase(t.clone()));
            }
        }
        Ok(())
    }

    pub fn check_events(&self) -> Result<(), EventCheckError> {
        let mut uniq = HashMap::new();
        for e in self.events.iter() {
            if let Some(prev_e) = uniq.insert(e.canonical_name(), e) {
                return Err(EventCheckError::DuplicateNameInSource(
                    prev_e.clone(),
                    e.clone(),
                ));
            }
        }

        for e in self.events.iter() {
            if e.name().to_uppercase() != e.name() {
                return Err(EventCheckError::NameNotUpperCase(e.clone()));
            }
        }

        Ok(())
    }

    pub fn merge_probes_into(&self, mut probe_id_gen: IdGen, mf_probes: &mut Probes) {
        let mut existing_probe_ids: Vec<u32> = mf_probes.iter().map(|p| p.id.0).collect();

        let mf_path = mf_probes.path.clone();
        self.probes.iter().for_each(|src_probe| {
            mf_probes
                .probes
                .iter_mut()
                .filter(|t| {
                    t.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_probe.canonical_name())
                })
                .for_each(|t| {
                    if !src_probe.eq(t) {
                        warn!(
                            "manifest-gen",
                            "Probe {}, ID {} may have moved\n\
                            Prior location from {}: {}:{}\n\
                            New location in source code: {}:{}:{}",
                            t.name,
                            t.id.0,
                            mf_path.display(),
                            t.file,
                            t.line,
                            src_probe.file.path,
                            src_probe.metadata.location.line,
                            src_probe.metadata.location.column
                        );

                        t.file = src_probe.file.path.clone();
                        t.line = src_probe.metadata.location.line.to_string();
                    }

                    let src_desc = src_probe
                        .metadata
                        .description
                        .as_ref()
                        .map_or("", |d| d.as_str());
                    if !t.description.as_str().eq(src_desc) {
                        t.description = String::from(src_desc);
                    }

                    let src_tags = src_probe.metadata.tags.as_ref().map_or("", |d| d.as_str());
                    if !t.tags.as_str().eq(src_tags) {
                        t.tags = String::from(src_tags);
                    }
                });
        });

        self.probes.iter().for_each(|src_probe| {
            let next_probe_id = Self::generate_probe_id(
                &mut probe_id_gen,
                src_probe.canonical_name().as_str(),
                &mut existing_probe_ids,
            );

            if mf_probes.probes.iter().find(|t| src_probe.eq(t)).is_none() {
                let probe = src_probe.to_probe(next_probe_id);
                println!(
                    "Adding probe {}, ID {} to {}",
                    probe.name,
                    probe.id.0,
                    mf_path.display(),
                );
                mf_probes.probes.push(probe);
            }
        });

        mf_probes.probes.iter().for_each(|mf_probe| {
            let missing_probe = self
                .probes
                .iter()
                .find(|t| {
                    mf_probe
                        .name
                        .as_str()
                        .eq_ignore_ascii_case(&t.canonical_name())
                })
                .is_none();
            if missing_probe {
                warn!(
                    "manifest-gen",
                    "Probe {}, ID {} in manifest no longer exists in source",
                    mf_probe.name,
                    mf_probe.id.0
                );
            }
        });
    }

    pub fn merge_events_into(&self, event_id_offset: Option<u32>, mf_events: &mut Events) {
        let mf_path = mf_events.path.clone();
        for src_event in self.events.iter() {
            mf_events
                .events
                .iter_mut()
                .filter(|e| {
                    e.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_event.canonical_name())
                })
                .for_each(|e| {
                    let file_eq = src_event.file.path.as_str().eq(e.file.as_str());
                    let line_eq = src_event
                        .metadata
                        .location
                        .line
                        .to_string()
                        .as_str()
                        .eq(e.line.as_str());
                    if !file_eq || !line_eq {
                        warn!(
                            "manifest-gen",
                            "Event {}, ID {} may have moved\n\
                            Prior location from {}: {}:{}\n\
                            New location in source code: {}:{}:{}",
                            e.name,
                            e.id.0,
                            mf_path.display(),
                            e.file,
                            e.line,
                            src_event.file.path,
                            src_event.metadata.location.line,
                            src_event.metadata.location.column
                        );
                        e.file = src_event.file.path.clone();
                        e.line = src_event.metadata.location.line.to_string();
                    }

                    if !e.type_hint.as_str().eq_ignore_ascii_case(
                        src_event
                            .metadata
                            .payload
                            .as_ref()
                            .map_or("", |p| p.0.as_str()),
                    ) {
                        warn!(
                            "manifest-gen",
                            "Event {}, ID {} has changed its payload type\n\
                            {}:{}:{}\n\
                            Prior payload type from {}: {}\n\
                            New payload type: {}",
                            e.name,
                            e.id.0,
                            src_event.file.path,
                            e.line,
                            src_event.metadata.location.column,
                            mf_path.display(),
                            e.type_hint,
                            src_event
                                .metadata
                                .payload
                                .as_ref()
                                .map_or(String::new(), |p| p.0.to_string())
                        );
                        e.type_hint = src_event
                            .metadata
                            .payload
                            .as_ref()
                            .map_or(String::new(), |p| p.0.to_string());
                    }

                    let src_desc = src_event
                        .metadata
                        .description
                        .as_ref()
                        .map_or("", |d| d.as_str());
                    if !e.description.as_str().eq(src_desc) {
                        e.description = String::from(src_desc);
                    }

                    let src_tags = src_event.metadata.tags.as_ref().map_or("", |d| d.as_str());
                    if !e.tags.as_str().eq(src_tags) {
                        e.tags = String::from(src_tags);
                    }
                });
        }

        self.internal_events
            .iter()
            .rev()
            .for_each(|internal_event| {
                if mf_events
                    .events
                    .iter()
                    .find(|e| internal_event.eq(e))
                    .is_none()
                {
                    mf_events.events.insert(0, internal_event.clone());
                }
            });

        let internal_events: Vec<u32> = self.internal_events.iter().map(|e| e.id.0).collect();
        let event_id_offset = event_id_offset.unwrap_or(0);
        let mut next_available_event_id: u32 =
            match mf_events.next_available_event_id(&internal_events) {
                id if event_id_offset > id => event_id_offset,
                id => id,
            };

        self.events.iter().for_each(|src_event| {
            if mf_events.events.iter().find(|e| src_event.eq(e)).is_none() {
                let event = src_event.to_event(EventId(next_available_event_id));
                println!(
                    "Adding event {}, ID {} to {}",
                    event.name,
                    event.id.0,
                    mf_path.display(),
                );
                mf_events.events.push(event);
                next_available_event_id += 1;
            }
        });

        mf_events
            .events
            .iter()
            .filter(|mf_event| !internal_events.contains(&mf_event.id.0))
            .for_each(|mf_event| {
                let missing_event = self
                    .events
                    .iter()
                    .find(|e| {
                        mf_event
                            .name
                            .as_str()
                            .eq_ignore_ascii_case(&e.canonical_name())
                    })
                    .is_none();
                if missing_event {
                    warn!(
                        "manifest-gen",
                        "Event {}, ID {} in manifest no longer exists in source",
                        mf_event.name,
                        mf_event.id.0
                    );
                }
            });
    }

    fn generate_probe_id(
        gen: &mut IdGen,
        probe_name: &str,
        existing_probe_ids: &mut Vec<u32>,
    ) -> ProbeId {
        let mut max_tries = std::u16::MAX;
        loop {
            let next_id = gen.hashed_id(probe_name);

            let id_already_taken = existing_probe_ids.iter().any(|&id| id == next_id.get());
            let is_valid_probe_id = modality_probe::ProbeId::new(next_id.get()).is_some();

            if !id_already_taken && is_valid_probe_id {
                existing_probe_ids.push(next_id.get());
                return ProbeId(next_id.get());
            }

            // Escape hatch
            max_tries = max_tries.saturating_sub(1);
            if max_tries == 0 {
                exit_error!("manifest-gen", "Exceeded the ProbeId hashing retry limit");
            }
        }
    }
}

fn is_hidden(entry: &DirEntry) -> bool {
    entry
        .file_name()
        .to_str()
        .map(|s| s.starts_with('.') && s != "." && s != "./")
        .unwrap_or(false)
}

impl fmt::Display for ProbeCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProbeCheckError::MultipleLocationsInSource(first, dup) => {
                writeln!(f, "Duplicate probe identifiers found for {}", first.name())?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    first.file.path, first.metadata.location.line, first.metadata.location.column
                )?;
                writeln!(f)?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    dup.file.path, dup.metadata.location.line, dup.metadata.location.column
                )
            }
            ProbeCheckError::NameNotUpperCase(t) => {
                writeln!(
                    f,
                    "The probe name '{}' needs to be converted to uppercase",
                    t.name(),
                )?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    t.file.path, t.metadata.location.line, t.metadata.location.column
                )
            }
        }
    }
}
impl fmt::Display for EventCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EventCheckError::DuplicateNameInSource(first, dup) => {
                writeln!(f, "Duplicate event identifiers found for {}", first.name())?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    first.file.path, first.metadata.location.line, first.metadata.location.column
                )?;
                writeln!(f)?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    dup.file.path, dup.metadata.location.line, dup.metadata.location.column
                )
            }
            EventCheckError::NameNotUpperCase(e) => {
                writeln!(
                    f,
                    "The event name '{}' needs to be converted to uppercase",
                    e.name(),
                )?;
                writeln!(
                    f,
                    "{}:{}:{}",
                    e.file.path, e.metadata.location.line, e.metadata.location.column
                )
            }
        }
    }
}

impl fmt::Display for CreationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CreationError::Parser(p, e) => {
                writeln!(f, "{}", e)?;
                writeln!(f, "{}:{}:{}", p, e.location().line, e.location().column)
            }
            CreationError::Io(p, t) => {
                writeln!(f, "{}", t)?;
                writeln!(f, "{}", p.display())
            }
            CreationError::FileDoesNotExist(p) => {
                write!(f, "Trying to resolve a nonexistent file")?;
                writeln!(f, "{}", p.display())
            }
            CreationError::NotRegularFile(p) => {
                write!(f, "Trying to resolve an irregular file")?;
                writeln!(f, "{}", p.display())
            }
        }
    }
}

impl From<file_path::Error> for CreationError {
    fn from(e: file_path::Error) -> Self {
        match e {
            file_path::Error::NotRegularFile(p) => CreationError::NotRegularFile(p),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::component::ComponentUuid;
    use crate::events::Event;
    use crate::manifest_gen::event_metadata::EventMetadata;
    use crate::manifest_gen::id_gen::NonZeroIdRange;
    use crate::manifest_gen::probe_metadata::ProbeMetadata;
    use crate::manifest_gen::type_hint::TypeHint;
    use crate::probes::Probe;
    use core::num::NonZeroU32;
    use pretty_assertions::assert_eq;

    #[test]
    fn probe_multi_location_file_error() {
        let loc_0 = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceProbe {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            probes: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_probes(),
            Err(ProbeCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn probe_multi_location_line_error() {
        let loc_0 = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 1).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            probes: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_probes(),
            Err(ProbeCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn probe_in_source_casing_error() {
        let loc_0 = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 3).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceProbe {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "location_b".to_string(),
                location: (4, 5, 6).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            probes: vec![loc_0, loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_probes(),
            Err(ProbeCheckError::NameNotUpperCase(loc_1))
        );
    }

    #[test]
    fn probe_merge_relocated() {
        let in_src_probe = InSourceProbe {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
                tags: None,
                description: None,
            },
        };
        let in_mf_probe = Probe {
            component_id: ComponentUuid::nil(),
            id: ProbeId(1),
            name: "location_a".to_string(),
            description: String::new(),
            tags: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            probes: vec![in_src_probe],
            events: Vec::new(),
            ..Default::default()
        };
        let mut mf_probes = Probes {
            path: PathBuf::new(),
            probes: vec![in_mf_probe.clone()],
        };
        let probe_id_range = NonZeroIdRange::new(
            NonZeroU32::new(1).unwrap(),
            NonZeroU32::new(modality_probe::ProbeId::MAX_ID).unwrap(),
        )
        .unwrap();
        let probe_id_gen = IdGen::new(probe_id_range);
        invcs.merge_probes_into(probe_id_gen, &mut mf_probes);
        assert_eq!(
            mf_probes.probes,
            vec![Probe {
                component_id: ComponentUuid::nil(),
                id: ProbeId(1),
                name: "location_a".to_string(),
                description: String::new(),
                tags: String::new(),
                file: "file.c".to_string(),
                line: "4".to_string(),
            }]
        );
    }

    #[test]
    fn probe_merge_tags_desc_change() {
        let in_src_probe = InSourceProbe {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: ProbeMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
                tags: Some("my-tag".to_string()),
                description: Some("desc".to_string()),
            },
        };
        let in_mf_probe = Probe {
            component_id: ComponentUuid::nil(),
            id: ProbeId(1),
            name: "location_a".to_string(),
            description: String::new(),
            tags: String::new(),
            file: "main.c".to_string(),
            line: "4".to_string(),
        };
        let invcs = Invocations {
            probes: vec![in_src_probe],
            events: Vec::new(),
            ..Default::default()
        };
        let mut mf_probes = Probes {
            path: PathBuf::new(),
            probes: vec![in_mf_probe.clone()],
        };
        let probe_id_range = NonZeroIdRange::new(
            NonZeroU32::new(1).unwrap(),
            NonZeroU32::new(modality_probe::ProbeId::MAX_ID).unwrap(),
        )
        .unwrap();
        let probe_id_gen = IdGen::new(probe_id_range);
        invcs.merge_probes_into(probe_id_gen, &mut mf_probes);
        assert_eq!(
            mf_probes.probes,
            vec![Probe {
                component_id: ComponentUuid::nil(),
                id: ProbeId(1),
                name: "location_a".to_string(),
                description: "desc".to_string(),
                tags: "my-tag".to_string(),
                file: "file.c".to_string(),
                line: "4".to_string(),
            }]
        );
    }

    #[test]
    fn event_in_source_casing_error() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "event_a".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![in_src_event.clone()],
            ..Default::default()
        };
        assert_eq!(
            invcs.check_events(),
            Err(EventCheckError::NameNotUpperCase(in_src_event))
        );
    }

    #[test]
    fn event_name_duplicate_error() {
        let e0 = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let e1 = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 3, 3).into(),
            },
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![e0.clone(), e1.clone()],
            ..Default::default()
        };
        assert_eq!(
            invcs.check_events(),
            Err(EventCheckError::DuplicateNameInSource(e0, e1))
        );
    }

    #[test]
    fn event_merge_file_location_change() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "file.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![in_src_event.clone()],
            ..Default::default()
        };
        let mut mf_events = Events {
            path: PathBuf::new(),
            events: vec![in_mf_event.clone()],
        };
        invcs.merge_events_into(None, &mut mf_events);
        let mut expected = Events::internal_events();
        expected.push(Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        });
        assert_eq!(mf_events.events, expected);
    }

    #[test]
    fn event_merge_line_location_change() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 8, 3).into(),
            },
        };
        let in_mf_event = Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![in_src_event.clone()],
            ..Default::default()
        };
        let mut mf_events = Events {
            path: PathBuf::new(),
            events: vec![in_mf_event.clone()],
        };
        invcs.merge_events_into(None, &mut mf_events);
        let mut expected = Events::internal_events();
        expected.push(Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "8".to_string(),
        });
        assert_eq!(mf_events.events, expected);
    }

    #[test]
    fn event_merge_type_hint_change() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: Some((TypeHint::U8, "mydata").into()),
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![in_src_event.clone()],
            ..Default::default()
        };
        let mut mf_events = Events {
            path: PathBuf::new(),
            events: vec![in_mf_event.clone()],
        };
        invcs.merge_events_into(None, &mut mf_events);
        let mut expected = Events::internal_events();
        expected.push(Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: "u8".to_string(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        });
        assert_eq!(mf_events.events, expected);
    }

    #[test]
    fn event_merge_tags_desc_change() {
        let in_src_event = InSourceEvent {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                probe_instance: "probe".to_string(),
                payload: None,
                description: Some("desc".to_string()),
                tags: Some("my-tag".to_string()),
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            probes: Vec::new(),
            events: vec![in_src_event.clone()],
            ..Default::default()
        };
        let mut mf_events = Events {
            path: PathBuf::new(),
            events: vec![in_mf_event.clone()],
        };
        invcs.merge_events_into(None, &mut mf_events);
        let mut expected = Events::internal_events();
        expected.push(Event {
            component_id: ComponentUuid::nil(),
            id: EventId(1),
            name: "event_a".to_string(),
            description: "desc".to_string(),
            tags: "my-tag".to_string(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        });
        assert_eq!(mf_events.events, expected);
    }
}
