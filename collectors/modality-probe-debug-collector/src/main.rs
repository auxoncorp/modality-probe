use std::sync::mpsc::channel;
use structopt::StructOpt;

mod cli;
use cli::{config_from_options, Opts};

use modality_probe_debug_collector::run;

fn main() {
    let opts = Opts::from_args();
    let config = match config_from_options(opts) {
        Ok(cfg) => cfg,
        Err(err) => {
            println!("{}", err);
            return;
        }
    };
    let (shutdown_sender, shutdown_receiver) = channel();
    ctrlc::set_handler(move || {
        println!();
        shutdown_sender.send(()).unwrap();
    })
    .expect("Could not set the Ctrl-C handler");
    if let Err(err) = run(&config, shutdown_receiver) {
        println!("{}", err);
    }
}
