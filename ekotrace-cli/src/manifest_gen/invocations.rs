use crate::manifest_gen::c_parser::CParser;
use crate::manifest_gen::in_source_event::InSourceEvent;
use crate::manifest_gen::in_source_tracer::InSourceTracer;
use crate::manifest_gen::parser::Parser;

use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{self, Read};
use std::path::Path;
use walkdir::WalkDir;

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
    ) -> io::Result<Self> {
        let mut tracers = Vec::new();
        let mut events = Vec::new();
        let mut buffer = String::new();
        for entry in WalkDir::new(p)
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
                    // error/warn if path resolution failed, default to file_name
                    // TODO - file path is relative to search dir
                    let file_path = entry.file_name().to_str().expect("TODO").to_string();

                    if !no_tracers {
                        let tracer_metadata =
                            CParser::default().parse_tracers(&buffer).expect("TODO");
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
                        let event_metadata =
                            CParser::default().parse_events(&buffer).expect("TODO");
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
}
