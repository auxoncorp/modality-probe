use crate::manifest_gen::{
    c_parser::CParser,
    file_path::{self, FilePath},
    in_source_event::InSourceEvent,
    in_source_tracer::InSourceTracer,
    parser::{self, Parser},
    rust_parser::RustParser,
};
use crate::{
    events::{EventId, Events},
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
    Io(io::Error),
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

pub struct Invocations {
    pub tracers: Vec<InSourceTracer>,
    pub events: Vec<InSourceEvent>,
}

impl Invocations {
    pub fn from_path<P: AsRef<Path>>(
        lang: Option<Lang>,
        no_tracers: bool,
        no_events: bool,
        p: P,
        file_extensions: &Option<Vec<String>>,
    ) -> Result<Self, CreationError> {
        let mut tracers = Vec::new();
        let mut events = Vec::new();
        let mut buffer = String::new();
        for entry in WalkDir::new(&p)
            .into_iter()
            .filter_entry(|e| !is_hidden(e))
            .filter_map(Result::ok)
            .filter(|e| !e.file_type().is_dir())
        {
            let should_consider = file_extensions.as_ref().map_or(true, |exts| {
                exts.iter()
                    .any(|ext| Some(OsStr::new(ext)) == entry.path().extension())
            });
            if should_consider {
                let mut f = File::open(entry.path())?;
                buffer.clear();

                // Skips binary/invalid data
                if f.read_to_string(&mut buffer).is_ok() {
                    if !entry.path().exists() {
                        return Err(CreationError::FileDoesNotExist(entry.path().to_path_buf()));
                    }

                    if !entry.path().is_file() {
                        return Err(CreationError::NotRegularFile(entry.path().to_path_buf()));
                    }

                    let search_path = p.as_ref().canonicalize()?;
                    let file = entry.path().canonicalize()?;
                    let file_path = FilePath::resolve(&search_path, &file)?;

                    let parser: Box<dyn Parser> = match lang {
                        Some(Lang::C) => Box::new(CParser::default()),
                        Some(Lang::Rust) => Box::new(RustParser::default()),
                        None => match entry.path().extension() {
                            Some(os_str) => match os_str.to_str() {
                                Some("rs") => Box::new(RustParser::default()),
                                Some("c") => Box::new(CParser::default()),
                                Some(ext) => {
                                    warn!(
                                        "manifest-gen",
                                        "Guessing C parser based on file extension '{}'", ext
                                    );
                                    Box::new(CParser::default())
                                }
                                None => {
                                    warn!(
                                        "manifest-gen",
                                        "Guessing C parser based on file extension '{}'",
                                        os_str.to_string_lossy()
                                    );
                                    Box::new(CParser::default())
                                }
                            },
                            None => {
                                warn!("manifest-gen",
                                    "No file extension available for '{:?}', defaulting to using the C parser",
                                    entry.path()
                                );
                                Box::new(CParser::default())
                            }
                        },
                    };

                    if !no_tracers {
                        let tracer_metadata = parser
                            .parse_tracers(&buffer)
                            .map_err(|e| CreationError::Parser(file_path.clone(), e))?;
                        let mut tracers_in_file: Vec<InSourceTracer> = tracer_metadata
                            .into_iter()
                            .map(|md| InSourceTracer {
                                file: file_path.clone(),
                                metadata: md,
                            })
                            .collect();
                        tracers.append(&mut tracers_in_file);
                    }

                    if !no_events {
                        let event_metadata = parser
                            .parse_events(&buffer)
                            .map_err(|e| CreationError::Parser(file_path.clone(), e))?;
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
        Ok(Invocations { tracers, events })
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
        self.tracers.iter().for_each(|src_tracer| {
            mf_tracers
                .0
                .iter_mut()
                .filter(|t| {
                    t.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_tracer.canonical_name())
                })
                .for_each(|t| {
                    if !src_tracer.eq(t) {
                        warn!(
                            "manifest-gen",
                            "Tracer {}, ID {} may have moved\n\
                            Prior location: {}:{}\n\
                            New location in source code: {}:{}",
                            t.name,
                            t.id.0,
                            t.file,
                            t.line,
                            src_tracer.file,
                            src_tracer.metadata.location.line
                        );

                        t.file = src_tracer.file.clone();
                        t.line = src_tracer.metadata.location.line.to_string();
                    }
                });
        });

        let tracer_id_offset = tracer_id_offset.unwrap_or(0);
        let mut next_available_tracer_id: u32 = match mf_tracers.next_available_tracer_id() {
            id if tracer_id_offset > id => tracer_id_offset,
            id => id,
        };

        self.tracers.iter().for_each(|src_tracer| {
            if mf_tracers.0.iter().find(|t| src_tracer.eq(t)).is_none() {
                mf_tracers
                    .0
                    .push(src_tracer.to_tracer(TracerId(next_available_tracer_id)));
                next_available_tracer_id += 1;
            }
        });

        mf_tracers.0.iter().for_each(|mf_tracer| {
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
                    "manifest-gen",
                    "Tracer {}, ID {} in manifest no longer exists in source",
                    mf_tracer.name,
                    mf_tracer.id.0
                );
            }
        });
    }

    pub fn merge_events_into(&self, event_id_offset: Option<u32>, mf_events: &mut Events) {
        for src_event in self.events.iter() {
            mf_events
                .0
                .iter_mut()
                .filter(|e| {
                    e.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_event.canonical_name())
                })
                .for_each(|e| {
                    let file_eq = src_event.file.as_str().eq(e.file.as_str());
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
                            Prior location: {}:{}\n\
                            New location in source code: {}:{}",
                            e.name,
                            e.id.0,
                            e.file,
                            e.line,
                            src_event.file,
                            src_event.metadata.location.line
                        );
                        e.file = src_event.file.clone();
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
                            {}:{}\n\
                            Prior payload type: {}\n\
                            New payload type: {}",
                            e.name,
                            e.id.0,
                            e.file,
                            e.line,
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

                    if Some(&e.description) != src_event.metadata.description.as_ref() {
                        if let Some(src_desc) = &src_event.metadata.description {
                            if src_desc != "" {
                                warn!(
                                    "manifest-gen",
                                    "Event {}, ID {} has changed its description\n\
                                    {}:{}\n\
                                    Prior description: '{}'\n\
                                    New description: '{}'",
                                    e.name,
                                    e.id.0,
                                    e.file,
                                    e.line,
                                    e.description,
                                    src_desc,
                                );
                                e.description = src_desc.clone();
                            }
                        }
                    }
                });
        }

        let event_id_offset = event_id_offset.unwrap_or(0);
        let mut next_available_event_id: u32 = match mf_events.next_available_event_id() {
            id if event_id_offset > id => event_id_offset,
            id => id,
        };

        self.events.iter().for_each(|src_event| {
            if mf_events.0.iter().find(|e| src_event.eq(e)).is_none() {
                mf_events
                    .0
                    .push(src_event.to_event(EventId(next_available_event_id)));
                next_available_event_id += 1;
            }
        });

        mf_events.0.iter().for_each(|mf_event| {
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
                writeln!(f, "{}:{}", first.file, first.metadata.location.line,)?;
                writeln!(f)?;
                writeln!(f, "{}:{}", dup.file, dup.metadata.location.line,)
            }
            TracerCheckError::NameNotUpperCase(t) => {
                writeln!(
                    f,
                    "The tracer name '{}' needs to be converted to uppercase",
                    t.name(),
                )?;
                writeln!(f, "{}:{}", t.file, t.metadata.location.line,)
            }
        }
    }
}
impl fmt::Display for EventCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EventCheckError::DuplicateNameInSource(first, dup) => {
                writeln!(f, "Duplicate event identifiers found for {}", first.name())?;
                writeln!(f, "{}:{}", first.file, first.metadata.location.line,)?;
                writeln!(f)?;
                writeln!(f, "{}:{}", dup.file, dup.metadata.location.line,)
            }
            EventCheckError::NameNotUpperCase(e) => {
                writeln!(
                    f,
                    "The event name '{}' needs to be converted to uppercase",
                    e.name(),
                )?;
                writeln!(f, "{}:{}", e.file, e.metadata.location.line,)
            }
        }
    }
}

impl fmt::Display for CreationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CreationError::Parser(file, e) => {
                writeln!(f, "{}", e)?;
                writeln!(f, "{}:{}", file, e.location().line)
            }
            CreationError::Io(t) => writeln!(f, "{}", t),
            CreationError::FileDoesNotExist(p) => {
                write!(f, "Trying to resolve a nonexistent file '{}'", p.display())
            }
            CreationError::NotRegularFile(p) => {
                write!(f, "Trying to resolve an irregular file '{}'", p.display())
            }
        }
    }
}

impl From<io::Error> for CreationError {
    fn from(e: io::Error) -> Self {
        CreationError::Io(e)
    }
}

impl From<(String, parser::Error)> for CreationError {
    fn from(e: (String, parser::Error)) -> Self {
        CreationError::Parser(e.0, e.1)
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
            file: "main.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
            },
        };
        let loc_1 = InSourceTracer {
            file: "file.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn tracer_multi_location_line_error() {
        let loc_0 = InSourceTracer {
            file: "main.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 1, 1).into(),
            },
        };
        let loc_1 = InSourceTracer {
            file: "main.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 1).into(),
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0.clone(), loc_1.clone()],
            events: Vec::new(),
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::MultipleLocationsInSource(loc_0, loc_1))
        );
    }

    #[test]
    fn tracer_in_source_casing_error() {
        let loc_0 = InSourceTracer {
            file: "main.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 2, 3).into(),
            },
        };
        let loc_1 = InSourceTracer {
            file: "main.c".to_string(),
            metadata: TracerMetadata {
                name: "location_b".to_string(),
                location: (4, 5, 6).into(),
            },
        };
        let invcs = Invocations {
            tracers: vec![loc_0, loc_1.clone()],
            events: Vec::new(),
        };
        assert_eq!(
            invcs.check_tracers(),
            Err(TracerCheckError::NameNotUpperCase(loc_1))
        );
    }

    #[test]
    fn tracer_merge_relocated() {
        let in_src_tracer = InSourceTracer {
            file: "file.c".to_string(),
            metadata: TracerMetadata {
                name: "LOCATION_A".to_string(),
                location: (1, 4, 3).into(),
            },
        };
        let in_mf_tracer = Tracer {
            id: TracerId(1),
            name: "location_a".to_string(),
            description: String::new(),
            file: "main.c".to_string(),
            function: String::new(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: vec![in_src_tracer],
            events: Vec::new(),
        };
        let mut mf_tracers = Tracers(vec![in_mf_tracer.clone()]);
        invcs.merge_tracers_into(None, &mut mf_tracers);
        assert_eq!(
            mf_tracers.0,
            vec![Tracer {
                id: TracerId(1),
                name: "location_a".to_string(),
                description: String::new(),
                file: "file.c".to_string(),
                function: String::new(),
                line: "4".to_string(),
            }]
        );
    }

    #[test]
    fn event_in_source_casing_error() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                description: None,
                location: (1, 2, 3).into(),
            },
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![in_src_event.clone()],
        };
        assert_eq!(
            invcs.check_events(),
            Err(EventCheckError::NameNotUpperCase(in_src_event))
        );
    }

    #[test]
    fn event_name_duplicate_error() {
        let e0 = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                description: None,
                location: (1, 2, 3).into(),
            },
        };
        let e1 = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                description: None,
                location: (1, 3, 3).into(),
            },
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![e0.clone(), e1.clone()],
        };
        assert_eq!(
            invcs.check_events(),
            Err(EventCheckError::DuplicateNameInSource(e0, e1))
        );
    }

    #[test]
    fn event_merge_file_location_change() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                description: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            type_hint: String::new(),
            file: "file.c".to_string(),
            function: String::new(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![in_src_event.clone()],
        };
        let mut mf_events = Events(vec![in_mf_event.clone()]);
        invcs.merge_events_into(None, &mut mf_events);
        assert_eq!(
            mf_events.0,
            vec![Event {
                id: EventId(1),
                name: "event_a".to_string(),
                description: String::new(),
                type_hint: String::new(),
                file: "main.c".to_string(),
                function: String::new(),
                line: "2".to_string(),
            }]
        );
    }

    #[test]
    fn event_merge_line_location_change() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                description: None,
                location: (1, 8, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            function: String::new(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![in_src_event.clone()],
        };
        let mut mf_events = Events(vec![in_mf_event.clone()]);
        invcs.merge_events_into(None, &mut mf_events);
        assert_eq!(
            mf_events.0,
            vec![Event {
                id: EventId(1),
                name: "event_a".to_string(),
                description: String::new(),
                type_hint: String::new(),
                file: "main.c".to_string(),
                function: String::new(),
                line: "8".to_string(),
            }]
        );
    }

    #[test]
    fn event_merge_type_hint_change() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "EVENT_A".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: Some((TypeHint::U8, "mydata").into()),
                description: None,
                location: (1, 2, 3).into(),
            },
        };
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_a".to_string(),
            description: String::new(),
            type_hint: String::new(),
            file: "main.c".to_string(),
            function: String::new(),
            line: "2".to_string(),
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![in_src_event.clone()],
        };
        let mut mf_events = Events(vec![in_mf_event.clone()]);
        invcs.merge_events_into(None, &mut mf_events);
        assert_eq!(
            mf_events.0,
            vec![Event {
                id: EventId(1),
                name: "event_a".to_string(),
                description: String::new(),
                type_hint: "u8".to_string(),
                file: "main.c".to_string(),
                function: String::new(),
                line: "2".to_string(),
            }]
        );
    }
}
