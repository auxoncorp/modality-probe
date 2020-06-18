use modality_probe_cli::{export, header_gen, manifest_gen, opts::*};
use structopt::StructOpt;

fn main() {
    let opts = Opts::from_args();

    let internal_events: Vec<u32> = modality_probe::EventId::INTERNAL_EVENTS
        .iter()
        .map(|id| id.get_raw())
        .collect();

    match opts {
        Opts::ManifestGen(opt) => manifest_gen::run(opt.into()),
        Opts::HeaderGen(opt) => header_gen::run(opt.into(), internal_events),
        Opts::Export(exp) => {
            if let Err(e) = export::run(exp) {
                println!("Error: {}", e);
            }
        }
    }
}
