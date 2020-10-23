#![allow(dead_code)]

use structopt::{clap::Shell, StructOpt};

mod component;
mod error;
mod events;
mod header_gen;
mod lang;
mod log;
mod manifest_gen;
mod meta;
mod opts;
mod probes;
mod visualize;

fn main() {
    // Generate `bash` completions in the current working directory
    opts::Opts::clap().gen_completions("modality-probe", Shell::Bash, "./");
}
