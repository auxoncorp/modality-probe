#![allow(dead_code)]

use structopt::{clap::Shell, StructOpt};

mod error;
mod events;
mod export;
mod header_gen;
mod lang;
mod manifest_gen;
mod opts;
mod probes;

fn main() {
    // Generate `bash` completions in the current working directory
    opts::Opts::clap().gen_completions("modality-probe", Shell::Bash, "./");
}
