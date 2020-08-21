use modality_probe_cli::{error::GracefulExit, export, header_gen, manifest_gen, opts::Opts};
use structopt::StructOpt;

fn main() {
    let opts = Opts::from_args();

    let internal_events: Vec<u32> = modality_probe::EventId::INTERNAL_EVENTS
        .iter()
        .map(|id| id.get_raw())
        .collect();

    match opts {
        Opts::ManifestGen(opt) => manifest_gen::run(opt),
        Opts::HeaderGen(opt) => header_gen::run(opt, internal_events),
        Opts::Export(opt) => export::run(opt).unwrap_or_exit("export"),
    }
}
