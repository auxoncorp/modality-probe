#![allow(dead_code)]

use structopt::{clap::Shell, StructOpt};

mod cli;

fn main() {
    // Generate `bash` completions in the current working directory
    cli::Opts::clap().gen_completions("modality-probe-debug-collector", Shell::Bash, "./");
}
