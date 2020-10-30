#![allow(dead_code)]

use modality_probe_offline_batch_collector::Opts;
use structopt::{clap::Shell, StructOpt};

fn main() {
    // Generate `bash` completions in the current working directory
    Opts::clap().gen_completions("modality-probe-offline-batch-collector", Shell::Bash, "./");
}
