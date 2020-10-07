#![deny(warnings)]

use std::io::{self, Read};
use std::{env, fs};

use log::info;
use modality_probe_collector_common::SessionId;
use structopt::StructOpt;

use modality_probe_offline_batch_collector::{OfflineBatchCollector, Opts};

fn main() -> io::Result<()> {
    env_logger::from_env(env_logger::Env::default().default_filter_or("info")).init();
    let opts = Opts::from_args();
    let session_id = SessionId::from(opts.session_id);
    let output_file = opts.output_file.unwrap_or_else(|| {
        env::current_dir()
            .expect("Could not retrieve current directory")
            .join(format!("session_{}_log_entries.jsonl", session_id.0))
    });

    let mut log_output_writer = fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&output_file)?;

    let reader: Box<dyn Read> = match opts.input_path {
        None => {
            info!("Reading from stdin");
            Box::new(io::stdin())
        }
        Some(input_file) => {
            info!("Reading from {}", input_file.display());
            Box::new(fs::File::open(input_file)?)
        }
    };

    let collector = OfflineBatchCollector::new(session_id, reader, &mut log_output_writer);

    let metrics = collector.run()?;

    let num_probes = metrics.probe_report_metrics.keys().count();
    let num_reports: u64 = metrics
        .probe_report_metrics
        .values()
        .map(|m| m.num_reports)
        .sum();

    info!(
        "Collected {} reports from {} probes in {}, {} reports were discarded",
        num_reports,
        num_probes,
        output_file.display(),
        metrics.reports_discarded,
    );

    info!(
        "Processed {} bytes, {} bytes were discarded",
        metrics.bytes_accumulated, metrics.bytes_discarded,
    );

    for (probe_id, m) in metrics.probe_report_metrics.iter() {
        info!(
            "{} reports from ProbeId {}, {} missed reports",
            m.num_reports,
            probe_id.get(),
            m.missed_seq_nums
        );
    }

    Ok(())
}
