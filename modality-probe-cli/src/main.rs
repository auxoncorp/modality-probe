use modality_probe_cli::{
    error::GracefulExit, header_gen, log, manifest_gen, opts::Opts, visualize,
};
use structopt::StructOpt;

fn main() {
    if let Err(e) = reset_signal_pipe_handler() {
        println!("Error: {}", e);
        std::process::exit(1);
    }

    let opts = Opts::from_args();

    match opts {
        Opts::ManifestGen(opt) => manifest_gen::run(opt, None),
        Opts::HeaderGen(opt) => header_gen::run(opt, None),
        Opts::Log(opt) => log::run(opt).unwrap_or_exit("log"),
        Opts::Visualize(opt) => visualize::run(opt).unwrap_or_exit("visualize"),
    }
}

// Used to prevent panics on broken pipes.
// See:
//   https://github.com/rust-lang/rust/issues/46016#issuecomment-605624865
fn reset_signal_pipe_handler() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(target_family = "unix")]
    {
        use nix::sys::signal;

        unsafe {
            signal::signal(signal::Signal::SIGPIPE, signal::SigHandler::SigDfl)?;
        }
    }

    Ok(())
}
