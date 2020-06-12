use structopt::StructOpt;

mod cli;
use cli::{CLIOptions, config_from_options};

fn main() {
    let opts = CLIOptions::from_args();
    let config = config_from_options(opts);
    println!("Running debug collector with configuration: {:#?}", config);
}

