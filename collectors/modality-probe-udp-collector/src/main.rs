#[cfg(feature = "cli")]
use structopt::StructOpt;

fn main() {
    #[cfg(not(feature = "cli"))]
    let opts = modality_probe_udp_collector::Opts::default();
    #[cfg(feature = "cli")]
    let opts = modality_probe_udp_collector::Opts::from_args();

    let config: modality_probe_udp_collector::Config = opts.into();
    println!("Using the configuration:");
    println!("    addr:\t\t{}", config.addr);
    println!("    session id:\t\t{}", config.session_id.0);
    println!("    output file:\t{}", config.output_file.display());
    let (_shutdown_sender, shutdown_receiver) =
        modality_probe_udp_collector::ShutdownSignalSender::new(config.addr);
    modality_probe_udp_collector::start_receiving(config, shutdown_receiver)
        .expect("Could not set up UDP Socket");
}
