use ekotrace_cli::{analysis, header_gen, lang::Lang, manifest_gen};
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "ekotrace", about = "Ekotrace command line interface")]
enum Opt {
    /// Generate event and tracer id manifest files from tracer event recording invocations
    ManifestGen(ManifestGen),

    /// Generate Rust/C header files with event/tracer id constants
    HeaderGen(HeaderGen),

    /// Analyze 'Ekotrace' event logs
    Analysis(Analysis),
}

#[derive(Debug, StructOpt)]
pub struct ManifestGen {
    /// Language (C or Rust), if not specified then guess based on file extensions
    #[structopt(short, long, parse(try_from_str))]
    lang: Option<Lang>,

    /// Event ID offset
    #[structopt(long)]
    event_id_offset: Option<u32>,

    /// Tracer ID offset
    #[structopt(long)]
    tracer_id_offset: Option<u32>,

    /// Limit the source code searching to files with matching extensions
    #[structopt(long = "file-extension")]
    file_extensions: Option<Vec<String>>,

    /// Event ID manifest CSV file
    #[structopt(long, parse(from_os_str), default_value = "events.csv")]
    events_csv_file: PathBuf,

    /// Tracer ID manifest CSV file
    #[structopt(long, parse(from_os_str), default_value = "tracers.csv")]
    tracers_csv_file: PathBuf,

    /// Omit generating event ID manifest
    #[structopt(long)]
    no_events: bool,

    /// Omit generating tracer ID manifest
    #[structopt(long)]
    no_tracers: bool,

    /// Source code path to search
    #[structopt(parse(from_os_str))]
    source_path: PathBuf,
}

#[derive(Debug, StructOpt)]
pub struct HeaderGen {
    /// Events csv file
    #[structopt(parse(from_os_str))]
    events_csv_file: PathBuf,

    /// Tracers csv file
    #[structopt(parse(from_os_str))]
    tracers_csv_file: PathBuf,

    #[structopt(short, long, parse(try_from_str), default_value = "C")]
    lang: Lang,

    /// C header include guard prefix
    #[structopt(long, default_value = "EKOTRACE")]
    include_guard_prefix: String,
}

#[derive(Debug, StructOpt)]
enum Analysis {
    SessionSummary {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,
    },

    /// Produce a graphviz (.dot) formatted graph of log segments and direct
    /// causal relationships. The .dot source is printed to standard out.
    SegmentGraph {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,

        /// The session to graph
        session_id: u32,
    },

    /// Produce a graphviz (.dot) formatted graph of log events and direct
    /// causal relationships. The .dot source is printed to standard out.
    EventGraph {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,

        /// The session to graph
        session_id: u32,
    },

    /// See if event A is caused by (is a causal descendant of) event B. Events
    /// are identified by "<session id>.<segment id>.<segment index>".
    QueryCausedBy {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,

        event_a: analysis::EventCoordinates,
        event_b: analysis::EventCoordinates,
    },
}

impl From<ManifestGen> for manifest_gen::Opt {
    fn from(opt: ManifestGen) -> Self {
        manifest_gen::Opt {
            lang: opt.lang,
            event_id_offset: opt.event_id_offset,
            tracer_id_offset: opt.tracer_id_offset,
            file_extensions: opt.file_extensions,
            events_csv_file: opt.events_csv_file,
            tracers_csv_file: opt.tracers_csv_file,
            no_events: opt.no_events,
            no_tracers: opt.no_tracers,
            source_path: opt.source_path,
        }
    }
}

impl From<HeaderGen> for header_gen::Opt {
    fn from(opt: HeaderGen) -> Self {
        header_gen::Opt {
            events_csv_file: opt.events_csv_file,
            tracers_csv_file: opt.tracers_csv_file,
            lang: opt.lang,
            include_guard_prefix: opt.include_guard_prefix,
        }
    }
}

impl From<Analysis> for analysis::Opt {
    fn from(opt: Analysis) -> Self {
        match opt {
            Analysis::SessionSummary { event_log_csv_file } => {
                analysis::Opt::SessionSummary { event_log_csv_file }
            }
            Analysis::SegmentGraph {
                event_log_csv_file,
                session_id,
            } => analysis::Opt::SegmentGraph {
                event_log_csv_file,
                session_id,
            },
            Analysis::EventGraph {
                event_log_csv_file,
                session_id,
            } => analysis::Opt::EventGraph {
                event_log_csv_file,
                session_id,
            },
            Analysis::QueryCausedBy {
                event_log_csv_file,
                event_a,
                event_b,
            } => analysis::Opt::QueryCausedBy {
                event_log_csv_file,
                event_a,
                event_b,
            },
        }
    }
}

fn main() {
    let opt = Opt::from_args();

    match opt {
        Opt::ManifestGen(opt) => manifest_gen::run(opt.into()),
        Opt::HeaderGen(opt) => header_gen::run(opt.into()),
        Opt::Analysis(opt) => analysis::run(opt.into()),
    }
}
