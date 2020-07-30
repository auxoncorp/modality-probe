#![allow(dead_code)]

#[cfg(feature = "cli")]
use structopt::{clap::Shell, StructOpt};

fn main() {
    // Generate `bash` completions in the current working directory
    #[cfg(feature = "cli")]
    modality_probe_udp_collector::Opts::clap().gen_completions(
        "modality-probe-udp-collector",
        Shell::Bash,
        "./",
    );
}
