use modality_probe_cli::{
    export::{self, Export},
    header_gen,
    lang::Lang,
    manifest_gen,
};
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "modality-probe",
    about = "Modality probe command line interface"
)]
enum Opt {
    /// Generate event and probe id manifest files from probe macro invocations
    ManifestGen(ManifestGen),

    /// Generate Rust/C header files with event/probe id constants
    HeaderGen(HeaderGen),

    /// Export a collected event log in a well-known graph format.
    Export(Export),
}

#[derive(Debug, StructOpt)]
pub struct ManifestGen {
    /// Language (C or Rust), if not specified then guess based on file extensions
    #[structopt(short, long, parse(try_from_str))]
    lang: Option<Lang>,

    /// Event ID offset
    #[structopt(long)]
    event_id_offset: Option<u32>,

    /// Probe ID offset
    #[structopt(long)]
    probe_id_offset: Option<u32>,

    /// Limit the source code searching to files with matching extensions
    #[structopt(long = "file-extension")]
    file_extensions: Option<Vec<String>>,

    /// Event ID manifest CSV file
    #[structopt(long, parse(from_os_str), default_value = "events.csv")]
    events_csv_file: PathBuf,

    /// Probe ID manifest CSV file
    #[structopt(long, parse(from_os_str), default_value = "probes.csv")]
    probes_csv_file: PathBuf,

    /// Omit generating event ID manifest
    #[structopt(long)]
    no_events: bool,

    /// Omit generating probe ID manifest
    #[structopt(long)]
    no_probes: bool,

    /// Source code path to search
    #[structopt(parse(from_os_str))]
    source_path: PathBuf,
}

#[derive(Debug, StructOpt)]
pub struct HeaderGen {
    /// Events csv file
    #[structopt(parse(from_os_str))]
    events_csv_file: PathBuf,

    /// Probes csv file
    #[structopt(parse(from_os_str))]
    probes_csv_file: PathBuf,

    #[structopt(short, long, parse(try_from_str), default_value = "C")]
    lang: Lang,

    /// C header include guard prefix
    #[structopt(long, default_value = "MODALITY_PROBE")]
    include_guard_prefix: String,

    /// Write output to file (instead of stdout)
    #[structopt(short = "o", long, parse(from_os_str))]
    output_path: Option<PathBuf>,
}

impl From<ManifestGen> for manifest_gen::Opt {
    fn from(opt: ManifestGen) -> Self {
        manifest_gen::Opt {
            lang: opt.lang,
            event_id_offset: opt.event_id_offset,
            probe_id_offset: opt.probe_id_offset,
            file_extensions: opt.file_extensions,
            events_csv_file: opt.events_csv_file,
            probes_csv_file: opt.probes_csv_file,
            no_events: opt.no_events,
            no_probes: opt.no_probes,
            source_path: opt.source_path,
        }
    }
}

impl From<HeaderGen> for header_gen::Opt {
    fn from(opt: HeaderGen) -> Self {
        header_gen::Opt {
            events_csv_file: opt.events_csv_file,
            probes_csv_file: opt.probes_csv_file,
            lang: opt.lang,
            include_guard_prefix: opt.include_guard_prefix,
            output_path: opt.output_path,
        }
    }
}

fn main() {
    let opt = Opt::from_args();

    let internal_events: Vec<u32> = modality_probe::EventId::INTERNAL_EVENTS
        .iter()
        .map(|id| id.get_raw())
        .collect();

    match opt {
        Opt::ManifestGen(opt) => manifest_gen::run(opt.into()),
        Opt::HeaderGen(opt) => header_gen::run(opt.into(), internal_events),
        Opt::Export(exp) => {
            if let Err(e) = export::run(exp) {
                println!("Error: {}", e);
            }
        }
    }
}
