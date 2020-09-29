use modality_probe_cli::{error::GracefulExit, export, header_gen, manifest_gen, opts::Opts};
use structopt::StructOpt;

fn main() {
    let opts = Opts::from_args();

    match opts {
        Opts::ManifestGen(opt) => manifest_gen::run(opt, None),
        Opts::HeaderGen(opt) => header_gen::run(opt, None),
        Opts::Export(opt) => export::run(opt).unwrap_or_exit("export"),
        Opts::Log(opt) => export::log(opt).unwrap_or_exit("export"),
    }
}
