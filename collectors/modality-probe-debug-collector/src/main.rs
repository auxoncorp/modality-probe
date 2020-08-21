use std::sync::mpsc::channel;
use structopt::StructOpt;

mod cli;
use cli::{config_from_options, CLIOptions};

use modality_probe_debug_collector::run;

fn main() {
    let opts = CLIOptions::from_args();
    let config = match config_from_options(opts) {
        Ok(cfg) => cfg,
        Err(err) => {
            println!("{}", err);
            return;
        }
    };
    let (_, shutdown_receiver) = channel();
    if let Err(err) = run(&config, shutdown_receiver) {
        println!("{}", err);
    }
}
