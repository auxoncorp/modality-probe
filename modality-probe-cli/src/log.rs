use std::{fs::File, path::PathBuf};

use structopt::StructOpt;

use modality_probe::ProbeId;
use modality_probe_collector_common::{json, LogEntryData};

use crate::{
    hopefully, hopefully_ok,
    meta::{self, EventMeta},
};

/// View the trace as a log.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Log {
    /// The probe to target. If no probe is given, the log from all
    /// probes is interleaved.
    #[structopt(short, long)]
    pub probe: String,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub components: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
}

pub fn run(l: Log) -> Result<(), Box<dyn std::error::Error>> {
    probe_log(l)
}

fn probe_log(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut l.components)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("failed to open the report file at {}", l.report.display())
    )?;

    let probe = match cfg.probes.iter().find(|(_, v)| v.name == l.probe) {
        Some((_, pm)) => pm,
        None => {
            let pid = hopefully!(
                l.probe.parse::<u32>(),
                format!("probe {} could not be found", l.probe)
            )?;
            hopefully_ok!(
                cfg.probes.get(&pid),
                format!("probe {} could not be found", l.probe)
            )?
        }
    };
    let pid = hopefully_ok!(
        ProbeId::new(probe.id),
        format!("encountered an invalid probe id {}", probe.id)
    )?;

    let mut log: Vec<_> = json::read_log_entries(&mut log_file)?
        .into_iter()
        .filter(|r| r.probe_id == pid && !r.is_frontier_clock())
        .collect();
    log.sort_by_key(|r| (r.sequence_number, r.sequence_index));

    for l in log {
        match l.data {
            LogEntryData::Event(id) => {
                let emeta = meta::get_event_meta(&cfg, &l.probe_id, &id)?;
                let probe_name = cfg
                    .probes
                    .get(&l.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", l.probe_id.get_raw()));
                print_log_line(emeta, &probe_name, None);
            }
            LogEntryData::EventWithPayload(id, pl) => {
                let emeta = meta::get_event_meta(&cfg, &l.probe_id, &id)?;
                let probe_name = cfg
                    .probes
                    .get(&l.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", l.probe_id.get_raw()));
                print_log_line(
                    emeta,
                    &probe_name,
                    meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), Some(pl))?,
                );
            }
            LogEntryData::TraceClock(lc) => {
                let probe_name = cfg
                    .probes
                    .get(&l.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", l.probe_id.get_raw()));
                let clock_probe_name = cfg
                    .probes
                    .get(&lc.id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", lc.id.get_raw()));
                println!(
                    "CLOCK ENTRY: {}@{} probe={}",
                    lc.pack().1,
                    clock_probe_name,
                    probe_name
                );
            }
            _ => (),
        }
    }
    Ok(())
}

fn print_log_line(emeta: &EventMeta, probe_name: &str, payload: Option<String>) {
    println!(
        "{} probe={} description={}{}{}tags={}{}",
        emeta.name,
        probe_name,
        emeta.description,
        if !emeta.file.is_empty() {
            format!(" file={} ", emeta.file)
        } else {
            " ".to_string()
        },
        if !emeta.line.is_empty() {
            format!(" line={} ", emeta.line)
        } else {
            " ".to_string()
        },
        emeta.tags,
        match payload {
            Some(p) => format!(" payload={}", p),
            None => " ".to_string(),
        }
    );
}
