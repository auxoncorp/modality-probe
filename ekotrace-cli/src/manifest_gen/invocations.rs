use crate::events::{Event, EventId, Events};
use crate::manifest_gen::{
    c_parser::{self, CParser},
    file_path::{self, FilePath},
    in_source_event::InSourceEvent,
    in_source_tracer::InSourceTracer,
    parser::Parser,
};
use crate::tracers::{TracerId, Tracers};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;
use std::fs::File;
use std::hash::Hash;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Debug)]
pub enum CreationError {
    Io(io::Error),
    Parser(c_parser::Error),
    FileDoesNotExist(PathBuf),
    NotRegularFile(PathBuf),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum TracerCheckError {
    MultipleLocationsInSource(InSourceTracer, InSourceTracer),
    NameNotUpperCase(InSourceTracer),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum EventMergeError {
    AssignedIdChanged(Event, InSourceEvent),
    AssignedIdConflictsWithManifest(Event, InSourceEvent),
}

pub struct Invocations {
    pub tracers: Vec<InSourceTracer>,
    pub events: Vec<InSourceEvent>,
}

impl Invocations {
    pub fn from_path<P: AsRef<Path>>(
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
            .filter_map(Result::ok)
            .filter(|e| !e.file_type().is_dir())
        {
            // Filter by file extensions, if provided
            if file_extensions.as_ref().map_or(true, |exts| {
                exts.iter()
                    .find(|&ext| Some(OsStr::new(ext)) == entry.path().extension())
                    .is_some()
            }) {
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

                    if !no_tracers {
                        let tracer_metadata = CParser::default().parse_tracers(&buffer)?;
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
                        let event_metadata = CParser::default().parse_events(&buffer)?;
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

    pub fn merge_tracers_into(&self, tracer_id_offset: Option<u32>, mf_tracers: &mut Tracers) {
        // Update existing tracer locations
        self.tracers.iter().for_each(|src_tracer| {
            mf_tracers
                .0
                .iter_mut()
                .find(|t| {
                    t.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_tracer.canonical_name())
                })
                .map(|t| {
                    if !src_tracer.eq(t) {
                        eprintln!("Relocating tracer '{}', ID {}", t.name, t.id.0);
                        eprintln!("Was in the manifest at {}:{}", t.file, t.line);
                        eprintln!(
                            "New location at {}:{}",
                            src_tracer.file, src_tracer.metadata.location.line
                        );

                        t.file = src_tracer.file.clone();
                        t.line = src_tracer.metadata.location.line.to_string();
                    }
                });
        });

        let tracer_id_offset = tracer_id_offset.unwrap_or(0);
        let mut next_available_tracer_id: u32 = match mf_tracers.next_available_tracer_id() {
            id if tracer_id_offset > id => tracer_id_offset,
            id @ _ => id,
        };

        // Add new tracers to the manifest
        self.tracers.iter().for_each(|src_tracer| {
            if mf_tracers.0.iter().find(|t| src_tracer.eq(t)).is_none() {
                mf_tracers
                    .0
                    .push(src_tracer.to_tracer(TracerId(next_available_tracer_id)));
                next_available_tracer_id += 1;
            }
        });
    }

    pub fn merge_events_into(
        &self,
        event_id_offset: Option<u32>,
        mf_events: &mut Events,
    ) -> Result<(), EventMergeError> {
        // Process assigned in-source events
        for src_event in self
            .events
            .iter()
            .filter(|src_event| src_event.is_assigned())
        {
            // Assigned events should exist in the manifest
            if mf_events
                .0
                .iter()
                .find(|e| {
                    e.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_event.canonical_name())
                })
                .is_none()
            {
                // Already checked in above `is_assigned()`
                let src_id = src_event.id().unwrap();

                eprintln!(
                    "Found an assigned event invocation ID {} that doesn't exist in the manfiest",
                    src_id.0
                );

                match mf_events.0.iter().find(|e| e.id == src_id) {
                    Some(e) => {
                        return Err(EventMergeError::AssignedIdConflictsWithManifest(
                            e.clone(),
                            src_event.clone(),
                        ));
                    }
                    None => {
                        eprintln!("Adding an entry to the manifest for ID {}", src_id.0);
                        mf_events.0.push(src_event.to_event(EventId(src_id.0)));
                    }
                }
            }

            // Check if the IDs have changed
            for e in mf_events.0.iter().filter(|e| src_event.eq(e)) {
                if src_event.id() != Some(e.id) {
                    return Err(EventMergeError::AssignedIdChanged(
                        e.clone(),
                        src_event.clone(),
                    ));
                }
            }

            // Check if the locations have changed
            mf_events
                .0
                .iter_mut()
                .filter(|e| {
                    e.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_event.canonical_name())
                })
                .filter(|e| src_event.id() == Some(e.id))
                .filter(|e| {
                    e.type_hint.as_str().eq_ignore_ascii_case(
                        src_event
                            .metadata
                            .payload
                            .as_ref()
                            .map_or("", |p| p.0.as_str()),
                    )
                })
                .for_each(|e| {
                    if !src_event.file.as_str().eq(e.file.as_str()) {
                        eprintln!("Relocating event '{}', ID {}", e.name, e.id.0);
                        eprintln!("Was in the manifest at {}:{}", e.file, e.line);
                        eprintln!(
                            "New location at {}:{}",
                            src_event.file, src_event.metadata.location.line
                        );
                        e.file = src_event.file.clone();
                    } else if !src_event
                        .metadata
                        .location
                        .line
                        .to_string()
                        .as_str()
                        .eq(e.line.as_str())
                    {
                        eprintln!("Relocating event '{}', ID {}", e.name, e.id.0);
                        eprintln!("Was in the manifest at {}:{}", e.file, e.line);
                        eprintln!(
                            "New location at {}:{}",
                            src_event.file, src_event.metadata.location.line
                        );
                        e.line = src_event.metadata.location.line.to_string();
                    }
                });

            // Check if the payload type hints have changed
            mf_events
                .0
                .iter_mut()
                .filter(|e| {
                    e.name
                        .as_str()
                        .eq_ignore_ascii_case(&src_event.canonical_name())
                })
                .filter(|e| src_event.id() == Some(e.id))
                .filter(|e| src_event.file.as_str().eq(e.file.as_str()))
                .filter(|e| {
                    src_event
                        .metadata
                        .location
                        .line
                        .to_string()
                        .as_str()
                        .eq(e.line.as_str())
                })
                .for_each(|e| {
                    if !e.type_hint.as_str().eq_ignore_ascii_case(
                        src_event
                            .metadata
                            .payload
                            .as_ref()
                            .map_or("", |p| p.0.as_str()),
                    ) {
                        eprintln!(
                            "Event '{}', ID {} has changed its payload type",
                            e.name, e.id.0
                        );
                        eprintln!("Was in the manifest as {}", e.type_hint);
                        e.type_hint = src_event
                            .metadata
                            .payload
                            .as_ref()
                            .map_or(String::new(), |p| p.0.to_string());
                        eprintln!("Now {}", e.type_hint);
                    }
                });
        }

        let event_id_offset = event_id_offset.unwrap_or(0);
        let mut next_available_event_id: u32 = match mf_events.next_available_event_id() {
            id if event_id_offset > id => event_id_offset,
            id @ _ => id,
        };

        // Add new unassigned events to the manifest
        self.events
            .iter()
            .filter(|src_event| !src_event.is_assigned())
            .for_each(|src_event| {
                if mf_events.0.iter().find(|e| src_event.eq(e)).is_none() {
                    mf_events
                        .0
                        .push(src_event.to_event(EventId(next_available_event_id)));
                    next_available_event_id += 1;
                }
            });

        Ok(())
    }

    pub fn check_tracers(&self) -> Result<(), TracerCheckError> {
        // Check the in-source tracers for unique invocations
        let mut uniq = HashMap::new();
        for t in self.tracers.iter() {
            if let Some(prev_t) = uniq.insert(t.canonical_name(), t) {
                return Err(TracerCheckError::MultipleLocationsInSource(
                    prev_t.clone(),
                    t.clone(),
                ));
            }
        }

        // The header-gen will make upper-case constants, check that the user's are
        // as well
        for t in self.tracers.iter() {
            if t.name().to_uppercase() != t.name() {
                return Err(TracerCheckError::NameNotUpperCase(t.clone()));
            }
        }

        Ok(())
    }
}

impl fmt::Display for TracerCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TracerCheckError::MultipleLocationsInSource(first, dup) => {
                writeln!(f, "Found an Ekotrace tracer used in multiple locations.")?;
                writeln!(f)?;
                writeln!(f, "First encounter:\n{}", first)?;
                writeln!(f)?;
                writeln!(f, "Duplicate:\n{}", dup)
            }
            TracerCheckError::NameNotUpperCase(t) => {
                writeln!(
                    f,
                    "Found an Ekotrace tracer token that needs to be converted to uppercase."
                )?;
                writeln!(f)?;
                writeln!(f, "{}", t)
            }
        }
    }
}

impl fmt::Display for CreationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CreationError::Parser(t) => writeln!(f, "{}", t),
            CreationError::Io(t) => writeln!(f, "{}", t),
            CreationError::FileDoesNotExist(p) => write!(
                f,
                "Trying to resolve a file '{}' that doesn't exist",
                p.display()
            ),
            CreationError::NotRegularFile(p) => write!(
                f,
                "Trying to resolve a file '{}' that isn't regular",
                p.display()
            ),
        }
    }
}

impl From<io::Error> for CreationError {
    fn from(e: io::Error) -> Self {
        CreationError::Io(e)
    }
}

impl From<c_parser::Error> for CreationError {
    fn from(e: c_parser::Error) -> Self {
        CreationError::Parser(e)
    }
}

impl From<file_path::Error> for CreationError {
    fn from(e: file_path::Error) -> Self {
        match e {
            file_path::Error::NotRegularFile(p) => CreationError::NotRegularFile(p),
        }
    }
}

impl fmt::Display for EventMergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EventMergeError::AssignedIdChanged(mf_e, src_e) => {
                writeln!(
                    f,
                    "The assigned event ID in-source has changed from what the manifest expects."
                )?;
                writeln!(f)?;
                writeln!(f, "Encountered:\n{}", src_e)?;
                writeln!(f)?;
                writeln!(f, "Expected:\n{}", mf_e)
            }
            EventMergeError::AssignedIdConflictsWithManifest(mf_e, src_e) => {
                writeln!(
                    f,
                    "Encountered and event ID in-source that doesn't exist in the manifest."
                )?;
                writeln!(
                    f,
                    "It's ID is occupied by another event so we can't use the ID."
                )?;
                writeln!(
                    f,
                    "Remove the assigned ID in-source and re-run the CLI to generate a new ID."
                )?;
                writeln!(f)?;
                writeln!(f, "Encountered:\n{}", src_e)?;
                writeln!(f)?;
                writeln!(f, "Conflicting event:\n{}", mf_e)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn event_merge_assigned_id_changed_error() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                assigned_id: Some(2),
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
        assert_eq!(
            invcs.merge_events_into(None, &mut mf_events),
            Err(EventMergeError::AssignedIdChanged(
                in_mf_event,
                in_src_event
            ))
        );
    }

    #[test]
    fn event_merge_assigned_in_src_but_not_in_manifest() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                assigned_id: Some(1),
                location: (1, 2, 3).into(),
            },
        };
        let invcs = Invocations {
            tracers: Vec::new(),
            events: vec![in_src_event.clone()],
        };
        let mut mf_events = Events(vec![]);
        // If the ID doesn't already exist in the manifest, then use it
        assert_eq!(invcs.merge_events_into(None, &mut mf_events), Ok(()));
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
        // If the ID is in use, throws an error
        let in_mf_event = Event {
            id: EventId(1),
            name: "event_b".to_string(),
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
        assert_eq!(
            invcs.merge_events_into(None, &mut mf_events),
            Err(EventMergeError::AssignedIdConflictsWithManifest(
                in_mf_event,
                in_src_event
            ))
        );
    }

    #[test]
    fn event_merge_file_location_change() {
        let in_src_event = InSourceEvent {
            file: "main.c".to_string(),
            metadata: EventMetadata {
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                assigned_id: Some(1),
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
        assert_eq!(invcs.merge_events_into(None, &mut mf_events), Ok(()));
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
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: None,
                assigned_id: Some(1),
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
        assert_eq!(invcs.merge_events_into(None, &mut mf_events), Ok(()));
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
                name: "event_a".to_string(),
                ekotrace_instance: "ekt".to_string(),
                payload: Some((TypeHint::U8, "mydata").into()),
                assigned_id: Some(1),
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
        assert_eq!(invcs.merge_events_into(None, &mut mf_events), Ok(()));
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
