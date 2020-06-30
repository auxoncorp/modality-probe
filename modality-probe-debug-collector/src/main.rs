use std::sync::mpsc::channel;
use structopt::StructOpt;

mod cli;
use cli::{config_from_options, CLIOptions};

use modality_probe_debug_collector::run;

fn main() {
    let opts = CLIOptions::from_args();
    let config = config_from_options(opts).unwrap();
    let (_, shutdown_receiver) = channel();
    run(&config, shutdown_receiver).unwrap();
}
