use std::path::PathBuf;

mod c_parser;
mod event_metadata;
mod in_source_event;
mod in_source_tracer;
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

// TODO - re-org the manifest_gen/* types
// the root CSV types need to change
// can they be the same? derive serde stuff

pub fn run(opt: Opt) {
    opt.validate();

    todo!();
}
