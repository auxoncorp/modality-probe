use std::{collections::HashMap, fs::File, path::PathBuf};

use structopt::StructOpt;

use modality_probe::ProbeId;
use modality_probe_collector_common::{json, LogEntryData};

use crate::{
    export::graph,
    hopefully, hopefully_ok,
    meta::{self, EventMeta},
};

/// Inspect the event log from the perspective of a single probe.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Log {
    /// The probe to target. If no probe is given, the log from all
    /// probes is interleaved.
    #[structopt(short, long)]
    pub probe: Option<String>,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub components: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
}

pub fn run(l: Log) -> Result<(), Box<dyn std::error::Error>> {
    match l.probe {
        Some(_) => probe_log(l),
        None => log_all(l),
    }
}

fn log_all(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut l.components)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("failed to open the report file at {}", l.report.display())
    )?;

    let report = json::read_log_entries(&mut log_file)?;
    let mut probes = HashMap::new();
    for ev in report {
        let p = probes.entry(ev.probe_id).or_insert_with(Vec::new);
        p.push(ev);
    }

    // Sort the probe-sorted events by sequence.
    for plog in probes.values_mut() {
        plog.sort_by_key(|p| std::cmp::Reverse((p.sequence_number, p.sequence_index)));
    }

    // Round-robin through the probe-sorted list and add events to the
    // log, interleaved probe by probe, but maintaining their total
    // order.
    let mut count = 0;
    loop {
        let init_count = count;
        for plog in probes.values_mut() {
            if let Some(l) = plog.pop() {
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
                            meta::parsed_payload(
                                emeta.type_hint.as_ref().map(|s| s.as_ref()),
                                Some(pl),
                            )?,
                        );
                    }
                    _ => (),
                }
                count += 1;
            }
        }
        if init_count == count {
            break;
        }
    }
    Ok(())
}

fn probe_log(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut l.components)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("failed to open the report file at {}", l.report.display())
    )?;

    let graph = graph::log_to_graph(
        json::read_log_entries(&mut log_file)?
            .into_iter()
            .peekable(),
    )?;

    let p = l.probe.expect("already checked that probe !None");

    let probe = match cfg.probes.iter().find(|(_, v)| v.name == p) {
        Some((_, pm)) => pm,
        None => {
            let pid = hopefully!(p.parse::<u32>(), format!("probe {} could not be found", p))?;
            hopefully_ok!(
                cfg.probes.get(&pid),
                format!("probe {} could not be found", p)
            )?
        }
    };
    let log = graph.graph.probe_log(hopefully_ok!(
        ProbeId::new(probe.id),
        format!(
            "encountered the invalid probe id {} when looking up probe {}",
            probe.id, p
        )
    )?);
    for l in log {
        let emeta = meta::get_event_meta(&cfg, &l.probe_id, &l.id)?;
        let probe_name = cfg
            .probes
            .get(&l.probe_id.get_raw())
            .map(|p| p.name.clone())
            .unwrap_or(format!("UNKNOWN_PROBE_{}", l.probe_id.get_raw()));
        print_log_line(
            emeta,
            &probe_name,
            meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), l.payload)?,
        );
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
            "".to_string()
        },
        if !emeta.line.is_empty() {
            format!(" line={} ", emeta.line)
        } else {
            "".to_string()
        },
        emeta.tags,
        match payload {
            Some(p) => format!(" payload={}", p),
            None => "".to_string(),
        }
    );
}
