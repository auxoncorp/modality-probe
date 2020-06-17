use crate::manifest_gen::{
    c_parser::CParser,
    file_path::{self, FilePath},
    in_source_event::InSourceEvent,
    in_source_tracer::InSourceTracer,
    parser::{self, Parser},
    rust_parser::RustParser,
};
use crate::{
    events::{Event, EventId, Events},
    lang::Lang,
    tracers::{TracerId, Tracers},
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
pub enum TracerCheckError {
    MultipleLocationsInSource(InSourceTracer, InSourceTracer),
    NameNotUpperCase(InSourceTracer),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum EventCheckError {
    DuplicateNameInSource(InSourceEvent, InSourceEvent),
    NameNotUpperCase(InSourceEvent),
}

pub struct Invocations<'cfg> {
    pub log_prefix: &'cfg str,
    pub log_module: &'cfg str,
    pub internal_events: Vec<Event>,
    pub tracers: Vec<InSourceTracer>,
    pub events: Vec<InSourceEvent>,
}

impl<'cfg> Default for Invocations<'cfg> {
    fn default() -> Self {
        let config = Config::default();
        Invocations {
            log_prefix: config.log_prefix,
            log_module: config.log_module,
            internal_events: config.internal_events,
            tracers: Default::default(),
            events: Default::default(),
        }
    }
}

pub struct Config<'cfg> {
    pub log_prefix: &'cfg str,
    pub log_module: &'cfg str,
    pub lang: Option<Lang>,
    pub no_tracers: bool,
    pub no_events: bool,
    pub c_parser: CParser<'cfg>,
    pub rust_parser: RustParser<'cfg>,
    pub file_extensions: Option<Vec<String>>,
    pub internal_events: Vec<Event>,
}

impl<'cfg> Default for Config<'cfg> {
    fn default() -> Self {
        Config {
            log_prefix: "modality-probe",
            log_module: "manifest-gen",
            lang: None,
            no_tracers: false,
            no_events: false,
            c_parser: CParser::default(),
            rust_parser: RustParser::default(),
            file_extensions: None,
            internal_events: Events::internal_events(),
        }
    }
}

impl<'cfg> Invocations<'cfg> {
    pub fn from_path<P: AsRef<Path>>(config: Config<'cfg>, p: P) -> Result<Self, CreationError> {
        let mut tracers = Vec::new();
        let mut events = Vec::new();
        let mut buffer = String::new();
        for entry in WalkDir::new(&p)
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
                buffer.clear();

                // Skips binary/invalid data
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
                                        config.log_prefix,
                                        config.log_module,
                                        "Guessing C parser based on file extension '{}'",
                                        ext
                                    );
                                    Box::new(config.c_parser)
                                }
                                None => {
                                    warn!(
                                        config.log_prefix,
                                        config.log_module,
                                        "Guessing C parser based on file extension '{}'",
                                        os_str.to_string_lossy()
                                    );
                                    Box::new(config.c_parser)
                                }
                            },
                            None => {
                                warn!(
                                    config.log_prefix,
                                    config.log_module,
                                    "No file extension available, defaulting to using the C parser\n\
                                    {:?}",
                                    entry.path()
                                );
                                Box::new(config.c_parser)
                            }
                        },
                    };

                    if !config.no_tracers {
                        let tracer_metadata = parser
                            .parse_tracers(&buffer)
                            .map_err(|e| CreationError::Parser(file_path.path.clone(), e))?;
                        let mut tracers_in_file: Vec<InSourceTracer> = tracer_metadata
                            .into_iter()
                            .map(|md| InSourceTracer {
                                file: file_path.clone(),
                                metadata: md,
                            })
                            .collect();
                        tracers.append(&mut tracers_in_file);
                    }

                    if !config.no_events {
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
        }
        Ok(Invocations {
            log_prefix: config.log_prefix,
            log_module: config.log_module,
            internal_events: config.internal_events,
            tracers,
            events,
        })
    }

    pub fn check_tracers(&self) -> Result<(), TracerCheckError> {
        let mut uniq = HashMap::new();
        for t in self.tracers.iter() {
            if let Some(prev_t) = uniq.insert(t.canonical_name(), t) {
                return Err(TracerCheckError::MultipleLocationsInSource(
                    prev_t.clone(),
                    t.clone(),
                ));
            }
        }

        for t in self.tracers.iter() {
            if t.name().to_uppercase() != t.name() {
                return Err(TracerCheckError::NameNotUpperCase(t.clone()));
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

    pub fn merge_tracers_into(&self, tracer_id_offset: Option<u32>, mf_tracers: &mut Tracers) {
        let mf_path = mf_tracers.path.clone();
        self.tracers.iter().for_each(|src_tracer| {
            mf_tracers
                .tracers
                .iter_mut()
                .filter(|t| {
                    t.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_tracer.canonical_name())
                })
                .for_each(|t| {
                    if !src_tracer.eq(t) {
                        warn!(
                            self.log_prefix,
                            self.log_module,
                            "Tracer {}, ID {} may have moved\n\
                            Prior location from {}: {}:{}\n\
                            New location in source code: {}:{}:{}",
                            t.name,
                            t.id.0,
                            mf_path.display(),
                            t.file,
                            t.line,
                            src_tracer.file.path,
                            src_tracer.metadata.location.line,
                            src_tracer.metadata.location.column
                        );

                        t.file = src_tracer.file.path.clone();
                        t.line = src_tracer.metadata.location.line.to_string();
                    }

                    let src_desc = src_tracer
                        .metadata
                        .description
                        .as_ref()
                        .map_or("", |d| d.as_str());
                    if !t.description.as_str().eq(src_desc) {
                        t.description = String::from(src_desc);
                    }

                    let src_tags = src_tracer.metadata.tags.as_ref().map_or("", |d| d.as_str());
                    if !t.tags.as_str().eq(src_tags) {
                        t.tags = String::from(src_tags);
                    }
                });
        });

        let tracer_id_offset = tracer_id_offset.unwrap_or(0);
        let mut next_available_tracer_id: u32 = match mf_tracers.next_available_tracer_id() {
            id if tracer_id_offset > id => tracer_id_offset,
            id => id,
        };

        self.tracers.iter().for_each(|src_tracer| {
            if mf_tracers
                .tracers
                .iter()
                .find(|t| src_tracer.eq(t))
                .is_none()
            {
                let tracer = src_tracer.to_tracer(TracerId(next_available_tracer_id));
                println!(
                    "Adding tracer {}, ID {} to {}",
                    tracer.name,
                    tracer.id.0,
                    mf_path.display(),
                );
                mf_tracers.tracers.push(tracer);
                next_available_tracer_id += 1;
            }
        });

        mf_tracers.tracers.iter().for_each(|mf_tracer| {
            let missing_tracer = self
                .tracers
                .iter()
                .find(|t| {
                    mf_tracer
                        .name
                        .as_str()
                        .eq_ignore_ascii_case(&t.canonical_name())
                })
                .is_none();
            if missing_tracer {
                warn!(
                    self.log_prefix,
                    self.log_module,
                    "Tracer {}, ID {} in manifest no longer exists in source",
                    mf_tracer.name,
                    mf_tracer.id.0
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
                            self.log_prefix,
                            self.log_module,
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
                            self.log_prefix,
                            self.log_module,
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
                        self.log_prefix,
                        self.log_module,
                        "Event {}, ID {} in manifest no longer exists in source",
                        mf_event.name,
                        mf_event.id.0
                    );
                }
            });
    }
}

fn is_hidden(entry: &DirEntry) -> bool {
    entry
        .file_name()
        .to_str()
        .map(|s| s.starts_with('.') && s != "." && s != "./")
        .unwrap_or(false)
}

impl fmt::Display for TracerCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TracerCheckError::MultipleLocationsInSource(first, dup) => {
                writeln!(f, "Duplicate tracer identifiers found for {}", first.name())?;
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
            TracerCheckError::NameNotUpperCase(t) => {
                writeln!(
                    f,
                    "The tracer name '{}' needs to be converted to uppercase",
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
    use crate::events::Event;
    use crate::manifest_gen::event_metadata::EventMetadata;
    use crate::manifest_gen::tracer_metadata::TracerMetadata;
    use crate::manifest_gen::type_hint::TypeHint;
    use crate::tracers::Tracer;
    use pretty_assertions::assert_eq;

    #[test]
    fn tracer_multi_location_file_error() {
        let loc_0 = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceTracer {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn tracer_multi_location_line_error() {
        let loc_0 = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 1).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn tracer_in_source_casing_error() {
        let loc_0 = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 3).into(),
                tags: None,
                description: None,
            },
        };
        let loc_1 = InSourceTracer {
            file: FilePath {
                full_path: "main.c".to_string(),
                path: "main.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "location_b".to_string(),
                location: (4, 5, 6).into(),
                tags: None,
                description: None,
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0, loc_1.clone()],
            events: Vec::new(),
            ..Default::default()
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::NameNotUpperCase(loc_1))
        );
    }

    #[test]
    fn tracer_merge_relocated() {
        let in_src_tracer = InSourceTracer {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
                tags: None,
                description: None,
            },
        };
        let in_mf_tracer = Tracer {
            id: TracerId(1),
            name: "location_a".to_string(),
            description: String::new(),
            tags: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: vec![in_src_tracer],
            events: Vec::new(),
            ..Default::default()
        };
        let mut mf_tracers = Tracers {
            path: PathBuf::new(),
            tracers: vec![in_mf_tracer.clone()],
        };
        invcs.merge_tracers_into(None, &mut mf_tracers);
        assert_eq!(
            mf_tracers.tracers,
            vec![Tracer {
                id: TracerId(1),
                name: "location_a".to_string(),
                description: String::new(),
                tags: String::new(),
                file: "file.c".to_string(),
                line: "4".to_string(),
            }]
        );
    }

    #[test]
    fn tracer_merge_tags_desc_change() {
        let in_src_tracer = InSourceTracer {
            file: FilePath {
                full_path: "file.c".to_string(),
                path: "file.c".to_string(),
            },
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
                tags: Some("my-tag".to_string()),
                description: Some("desc".to_string()),
            },
        };
        let in_mf_tracer = Tracer {
            id: TracerId(1),
            name: "location_a".to_string(),
            description: String::new(),
            tags: String::new(),
            file: "main.c".to_string(),
            line: "4".to_string(),
        };
        let invcs = Invocations {
            tracers: vec![in_src_tracer],
            events: Vec::new(),
            ..Default::default()
        };
        let mut mf_tracers = Tracers {
            path: PathBuf::new(),
            tracers: vec![in_mf_tracer.clone()],
        };
        invcs.merge_tracers_into(None, &mut mf_tracers);
        assert_eq!(
            mf_tracers.tracers,
            vec![Tracer {
                id: TracerId(1),
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
                agent_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
                agent_instance: "probe".to_string(),
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
                agent_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 3, 3).into(),
            },
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
                agent_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "file.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
                agent_instance: "probe".to_string(),
                payload: None,
                description: None,
                tags: None,
                location: (1, 8, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
                agent_instance: "probe".to_string(),
                payload: Some((TypeHint::U8, "mydata").into()),
                description: None,
                tags: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
                agent_instance: "probe".to_string(),
                payload: None,
                description: Some("desc".to_string()),
                tags: Some("my-tag".to_string()),
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            tags: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
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
