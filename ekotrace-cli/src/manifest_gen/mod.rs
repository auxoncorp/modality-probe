use crate::{error::GracefulExit, events::Events, exit_error, lang::Lang, tracers::Tracers};
use invocations::{Config, Invocations};
use std::path::PathBuf;

pub mod c_parser;
pub mod event_metadata;
pub mod file_path;
pub mod in_source_event;
pub mod in_source_tracer;
pub mod invocations;
pub mod parser;
pub mod rust_parser;
pub mod source_location;
pub mod tracer_metadata;
pub mod type_hint;

#[derive(Debug)]
pub struct Opt {
    pub lang: Option<Lang>,
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
                "ekotrace",
                "manifest-gen",
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

    let config = Config {
        lang: opt.lang,
        no_tracers: opt.no_tracers,
        no_events: opt.no_events,
        file_extensions: opt.file_extensions,
        ..Default::default()
    };

    let invocations =
        Invocations::from_path(config, opt.source_path).unwrap_or_exit("manifest-gen");

    invocations.check_tracers().unwrap_or_exit("manifest-gen");
    invocations.check_events().unwrap_or_exit("manifest-gen");

    invocations.merge_tracers_into(opt.tracer_id_offset, &mut manifest_tracers);
    invocations.merge_events_into(opt.event_id_offset, &mut manifest_events);

    // Write out the new events and tracers CSV files
    if !opt.no_events {
        manifest_events.write_csv(&opt.events_csv_file);
    }

    if !opt.no_tracers {
        manifest_tracers.write_csv(&opt.tracers_csv_file);
    }
}
