use crate::events::{Event, EventId, Events};
use crate::tracers::{Tracer, TracerId, Tracers};
use event_metadata::EventMetadata;
use in_source_event::InSourceEvent;
use invocations::Invocations;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use walkdir::WalkDir;

mod c_parser;
mod event_metadata;
mod in_source_event;
mod in_source_tracer;
mod invocations;
mod parser;
mod source_location;
mod tracer_metadata;
mod type_hint;

#[derive(Debug)]
pub struct Opt {
    pub event_id_offset: Option<u32>,
    pub tracer_id_offset: Option<u32>,
    pub file_extensions: Option<Vec<String>>,
    pub events_csv_file: PathBuf,
    pub tracers_csv_file: PathBuf,
    pub no_events: bool,
    pub no_tracers: bool,
    pub source_path: PathBuf,
}

impl Opt {
    pub fn validate(&self) {
        assert!(
            self.source_path.exists(),
            "Source path \"{}\" does not exist",
            self.source_path.display()
        );
    }
}

pub fn run(opt: Opt) {
    opt.validate();

    // Read in existing CSVs if they exists
    let mut csv_events = Events::from_csv(&opt.events_csv_file);
    let mut csv_tracers = Tracers::from_csv(&opt.tracers_csv_file);

    // TODO
    // Check existing events and tracers
    csv_events.validate_nonzero_ids();
    csv_events.validate_unique_ids();
    //csv_events.validate_unique_names();

    csv_tracers.validate_nonzero_ids();
    csv_tracers.validate_unique_ids();
    csv_tracers.validate_unique_names();

    // Collect event and tracer info in each source file
    let invocations = Invocations::from_path(
        opt.no_tracers,
        opt.no_events,
        opt.source_path,
        &opt.file_extensions,
    )
    .expect("TODO");

    // TODO
    //invocations.check_tracers();
    //invocations.check_events();

    // Generate tracer IDs for new tracers, with offset if provided
    let tracer_id_offset = opt.tracer_id_offset.unwrap_or(0);
    let mut next_available_tracer_id: u32 = match csv_tracers.next_available_tracer_id() {
        id if tracer_id_offset > id => tracer_id_offset,
        id @ _ => id,
    };

    // TODO will refactor this
    // Add new tracers to the CSV data
    invocations.tracers.iter().for_each(|src_tracer| {
        if csv_tracers
            .0
            .iter()
            .find(|csv_tracer| {
                csv_tracer
                    .name
                    .as_str()
                    .eq_ignore_ascii_case(src_tracer.metadata.name.as_str())
            })
            .is_none()
        {
            csv_tracers
                .0
                .push(src_tracer.to_tracer(TracerId(next_available_tracer_id)));
            next_available_tracer_id += 1;
        }
    });

    // Generate event IDs for new events, with offset if provided
    let event_id_offset = opt.event_id_offset.unwrap_or(0);
    let mut next_available_event_id: u32 = match csv_events.next_available_event_id() {
        id if event_id_offset > id => event_id_offset,
        id @ _ => id,
    };

    // TODO will refactor this
    // Add new events to the CSV data
    invocations.events.iter().for_each(|src_event| {
        if csv_events
            .0
            .iter()
            .find(|csv_event| src_event.eq(csv_event))
            .is_none()
        {
            csv_events
                .0
                .push(src_event.to_event(EventId(next_available_event_id)));
            next_available_event_id += 1;
        }
    });

    // Write out the new events and tracers CSV files
    if !opt.no_events {
        csv_events.into_csv(&opt.events_csv_file);
    }

    if !opt.no_tracers {
        csv_tracers.into_csv(&opt.tracers_csv_file);
    }
}
