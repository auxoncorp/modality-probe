use crate::{error::GracefulExit, events::Events, exit_error, lang::Lang, probes::Probes};
use invocations::{Config, Invocations};
use std::path::PathBuf;

pub mod c_parser;
pub mod event_metadata;
pub mod file_path;
pub mod in_source_event;
pub mod in_source_probe;
pub mod invocations;
pub mod parser;
pub mod probe_metadata;
pub mod rust_parser;
pub mod source_location;
pub mod type_hint;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Opt {
    pub lang: Option<Lang>,
    pub event_id_offset: Option<u32>,
    pub probe_id_offset: Option<u32>,
    pub file_extensions: Option<Vec<String>>,
    pub events_csv_file: PathBuf,
    pub probes_csv_file: PathBuf,
    pub no_events: bool,
    pub no_probes: bool,
    pub source_path: PathBuf,
}

impl Default for Opt {
    fn default() -> Self {
        Opt {
            lang: None,
            event_id_offset: None,
            probe_id_offset: None,
            file_extensions: None,
            events_csv_file: PathBuf::from("events.csv"),
            probes_csv_file: PathBuf::from("probes.csv"),
            no_events: false,
            no_probes: false,
            source_path: PathBuf::from("."),
        }
    }
}

impl Opt {
    pub fn validate(&self) {
        if !self.source_path.exists() {
            exit_error!(
                "modality-probe",
                "manifest-gen",
                "The source path '{}' does not exist",
                self.source_path.display()
            );
        }
    }
}

pub fn run(opt: Opt) {
    opt.validate();

    let mut manifest_probes = Probes::from_csv(&opt.probes_csv_file);
    let mut manifest_events = Events::from_csv(&opt.events_csv_file);

    manifest_probes.validate_nonzero_ids();
    manifest_probes.validate_unique_ids();
    manifest_probes.validate_unique_names();

    manifest_events.validate_nonzero_ids();
    manifest_events.validate_unique_ids();
    manifest_events.validate_unique_names();

    let config = Config {
        lang: opt.lang,
        no_probes: opt.no_probes,
        no_events: opt.no_events,
        file_extensions: opt.file_extensions,
        ..Default::default()
    };

    let invocations =
        Invocations::from_path(config, opt.source_path).unwrap_or_exit("manifest-gen");

    invocations.check_probes().unwrap_or_exit("manifest-gen");
    invocations.check_events().unwrap_or_exit("manifest-gen");

    invocations.merge_probes_into(opt.probe_id_offset, &mut manifest_probes);
    invocations.merge_events_into(opt.event_id_offset, &mut manifest_events);

    // Write out the new events and probes CSV files
    if !opt.no_events {
        manifest_events.write_csv(&opt.events_csv_file);
    }

    if !opt.no_probes {
        manifest_probes.write_csv(&opt.probes_csv_file);
    }
}
