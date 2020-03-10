use crate::error::GracefulExit;
use crate::events::Events;
use crate::exit_error;
use crate::tracers::Tracers;
use invocations::Invocations;
use std::path::PathBuf;

mod c_parser;
mod event_metadata;
mod file_path;
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
        if !self.source_path.exists() {
            exit_error!(
                "The source path '{}' does not exist",
                self.source_path.display()
            );
        }
    }
}

pub fn run(opt: Opt) {
    opt.validate();

    let mut manifest_tracers = Tracers::from_csv(&opt.tracers_csv_file);
    let mut manifest_events = Events::from_csv(&opt.events_csv_file);

    manifest_tracers.validate_nonzero_ids();
    manifest_tracers.validate_unique_ids();
    manifest_tracers.validate_unique_names();

    manifest_events.validate_nonzero_ids();
    manifest_events.validate_unique_ids();
    manifest_events.validate_unique_names();

    let invocations = Invocations::from_path(
        opt.no_tracers,
        opt.no_events,
        opt.source_path,
        &opt.file_extensions,
    )
    .unwrap_or_exit("Can't collect invocations");

    invocations
        .check_tracers()
        .unwrap_or_exit("Can't use the collected tracers");
    invocations
        .check_events()
        .unwrap_or_exit("Can't use the collected events");

    invocations.merge_tracers_into(opt.tracer_id_offset, &mut manifest_tracers);
    invocations.merge_events_into(opt.event_id_offset, &mut manifest_events);

    // Write out the new events and tracers CSV files
    if !opt.no_events {
        manifest_events.into_csv(&opt.events_csv_file);
    }

    if !opt.no_tracers {
        manifest_tracers.into_csv(&opt.tracers_csv_file);
    }
}
