use structopt::StructOpt;

mod cli;
use cli::{config_from_options, CLIOptions};

fn main() {
    let opts = CLIOptions::from_args();
    let config = config_from_options(opts);
    println!("Running debug collector with configuration: {:#?}", config);
}
