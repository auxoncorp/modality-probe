use std::{
    collections::{BTreeMap, HashMap},
    convert::TryFrom,
    fs::File,
    path::PathBuf,
};

use structopt::StructOpt;

use modality_probe::{EventId, ProbeId};
use modality_probe_collector_common::{json, LogEntryData, ReportLogEntry};

use crate::{
    description_format::DescriptionFormat,
    hopefully, hopefully_ok,
    meta::{self, Cfg},
};

mod color;
mod format;
mod graph;
mod radius;

use radius::Radius;

/// View the trace as a log.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Log {
    /// The probe to target. If no probe is given, the log from all
    /// probes is interleaved.
    #[structopt(long)]
    pub probe: Option<String>,
    /// The component to target. If no component is given, the log
    /// from all components is interleaved.
    #[structopt(long)]
    pub component: Option<String>,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub component_path: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
    /// Print the log as an ASCII-art graph.
    #[structopt(long)]
    pub graph: bool,
    /// Provide (more) verbose output.
    /// (-v, -vv, &c.)
    #[structopt(short, parse(from_occurrences))]
    pub verbose: u8,

    /// Provide a custom format string to be interpreted by each event
    /// row.
    ///
    /// The format string may use any combination of the following
    /// identifiers.
    ///
    /// | Specifier | Data               |
    /// |-----------|--------------------|
    /// |    %ei    | Event id           |
    /// |    %en    | Event name         |
    /// |    %ef    | Event file         |
    /// |    %el    | Event line         |
    /// |    %et    | Event tags         |
    /// |    %ed    | Event description  |
    /// |    %et    | Event type hint    |
    /// |    %ep    | Event payload      |
    /// |    %er    | Raw event payload  |
    /// |    %ec    | Event coordinate   |
    /// |    %eo    | Event clock offset |
    /// |    %pi    | Probe id           |
    /// |    %pn    | Probe name         |
    /// |    %pc    | Probe clock        |
    /// |    %pd    | Probe description  |
    /// |    %pf    | Probe file         |
    /// |    %pl    | Probe line         |
    /// |    %pt    | Probe tags         |
    /// |    %ci    | Component id       |
    /// |    %cn    | Component name     |
    /// |    %rt    | Receive time       |
    ///
    /// NOTE: If an identifier is used in the string and that field is not
    /// available on the event, it will be replaced by an empty string.
    #[structopt(short, long, verbatim_doc_comment)]
    pub format: Option<String>,

    /// Filter a whole graph down to the radius around a specific
    /// event.
    ///
    /// Takes a number used as the “size” of the radius—the number of
    /// events on any path in either direction that should be included
    /// in the output.
    ///
    /// Requires `--from`.
    #[structopt(long, requires = "from")]
    pub radius: Option<usize>,

    /// Provide an event coordinate as a starting point for the
    /// filters that require it.
    #[structopt(long)]
    pub from: Option<String>,

    /// Don't colorize the output.
    #[structopt(long)]
    pub no_color: bool,
}

pub fn run(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut l.component_path)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("Failed to open the report file at {}", l.report.display())
    )?;

    let report = json::read_log_entries(&mut log_file)?;
    let (probes, clock_rows) = sort_probes(&cfg, &l, report)?;

    let color_term = std::env::var("COLORTERM").unwrap_or_else(|_| String::new());
    if l.no_color || (color_term != "truecolor" && color_term != "24bit") {
        let mut b = hopefully!(
            color::COLORIZE.write(),
            "An internal error occurred before before printing the log"
        )?;
        *b = false;
    }

    if l.graph {
        graph::print_as_graph(probes, clock_rows, &cfg, &l, std::io::stdout())
    } else {
        print_as_log(probes, &l, &cfg)
    }
}

type SortedProbes = (BTreeMap<ProbeId, Vec<ReportLogEntry>>, Vec<ReportLogEntry>);

fn sort_probes(
    cfg: &Cfg,
    l: &Log,
    report: Vec<ReportLogEntry>,
) -> Result<SortedProbes, Box<dyn std::error::Error>> {
    let mut probes = BTreeMap::new();

    // If `--probe` was given, pare the trace down to just events from
    // a single probe. `clock_set` must be built off of the pared-down
    // set; it's what prevents the target probe's from getting
    // blocked.
    let pid = if let Some(ref p) = l.probe {
        let probe = match cfg.probes.iter().find(|(_, v)| v.name == *p) {
            Some((_, pm)) => pm,
            None => {
                let pid = hopefully!(p.parse::<u32>(), format!("Probe {} could not be found", p))?;
                hopefully_ok!(
                    cfg.probes.get(&pid),
                    format!("Probe {} could not be found", p)
                )?
            }
        };
        let pid = hopefully_ok!(
            ProbeId::new(probe.id),
            format!("Encountered an invalid probe id {}", probe.id)
        )?;
        Some(pid)
    } else {
        None
    };

    // If `--component` was given, pare the trace down to just events
    // from a single component. `clock_set` must be built off of the
    // pared-down set; it's what prevents the target component's
    // timelines from getting blocked.
    let cid = if let Some(ref c) = l.component {
        match cfg.component_names.get(c) {
            Some(_) => Some(c),
            None => cfg
                .component_names
                .iter()
                .find(|(_, name)| name == &c)
                .map(|(id, _)| id),
        }
    } else {
        None
    };

    match (cid, pid) {
        (Some(c), Some(p)) => {
            for ev in report {
                if let Some(id) = cfg.probes_to_components.get(&ev.probe_id.get_raw()) {
                    if ev.probe_id == p && &id.to_string() == c {
                        let p = probes.entry(ev.probe_id).or_insert_with(Vec::new);
                        if !ev.is_internal_event() {
                            p.push(ev);
                        }
                    }
                }
            }
        }
        (Some(c), None) => {
            for ev in report {
                if let Some(id) = cfg.probes_to_components.get(&ev.probe_id.get_raw()) {
                    if &id.to_string() == c {
                        let p = probes.entry(ev.probe_id).or_insert_with(Vec::new);
                        if !ev.is_internal_event() {
                            p.push(ev);
                        }
                    }
                }
            }
        }
        (None, Some(p)) => {
            for ev in report {
                if ev.probe_id == p {
                    let p = probes.entry(ev.probe_id).or_insert_with(Vec::new);
                    if !ev.is_internal_event() {
                        p.push(ev);
                    }
                }
            }
        }
        (None, None) => {
            for ev in report {
                let p = probes.entry(ev.probe_id).or_insert_with(Vec::new);
                if !ev.is_internal_event() {
                    p.push(ev);
                }
            }
        }
    }

    // Sort the probe-sorted events by sequence and peel off the
    // clocks. The clock set is used to determine that both ends of an
    // edge are present in the dataset. This prevents a given timeline
    // from being blocked and waiting indefinitely.
    let mut clock_rows = Vec::new();
    for plog in probes.values_mut() {
        plog.sort_by_key(|p| std::cmp::Reverse((p.sequence_number, p.sequence_index)));
        for r in plog.iter() {
            match r.data {
                LogEntryData::TraceClock(_) => clock_rows.push(r.clone()),
                LogEntryData::TraceClockWithTime(_, _) => clock_rows.push(r.clone()),
                _ => (),
            }
        }
    }
    if let (Some(ref r), Some(ref coord)) = (l.radius, l.from.as_ref()) {
        let radius = Radius::try_from((r, coord.as_ref()))?;
        return Ok(radius::truncate_to_radius((probes, clock_rows), radius));
    }

    Ok((probes, clock_rows))
}

fn print_as_log(
    mut probes: BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    l: &Log,
    cfg: &Cfg,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut count = 0;
    let indices = probes
        .keys()
        .enumerate()
        .map(|(idx, id)| (*id, idx))
        .collect::<HashMap<ProbeId, usize>>();
    'outer: loop {
        let init_count = count;
        for (idx, (probe_id, log)) in probes.iter_mut().enumerate() {
            let mut seen_self_clock = false;
            'inner: loop {
                if let Some(row) = log.pop() {
                    match row.data {
                        LogEntryData::Event(id) | LogEntryData::EventWithTime(.., id) => {
                            print_event_info(idx, row, &id, None, l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::EventWithPayload(id, pl)
                        | LogEntryData::EventWithPayloadWithTime(.., id, pl) => {
                            print_event_info(idx, row, &id, Some(pl), l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or_else(|| row.probe_id.get_raw().to_string());
                            if lc.id == *probe_id {
                                if !seen_self_clock {
                                    if l.verbose == 0 {
                                        println!();
                                    }
                                    println!(
                                        "Clock Tick @ {} {} clock=({}, {})",
                                        color::colorize_probe(idx, &probe_name),
                                        color::colorize_coord(&row.coordinate()),
                                        lc.epoch.0,
                                        lc.ticks.0
                                    );
                                    seen_self_clock = true;
                                    count += 1;
                                } else {
                                    log.push(row);
                                    count += 1;
                                    break 'inner;
                                }
                            } else {
                                let remote_probe_name = cfg
                                    .probes
                                    .get(&lc.id.get_raw())
                                    .map(|p| p.name.clone())
                                    .unwrap_or_else(|| row.probe_id.get_raw().to_string());
                                let remote_probe_idx = indices.get(&lc.id);
                                println!(
                                    "Snapshot Merge @ {} ({}), from={} clock=({}, {})",
                                    color::colorize_probe(idx, &probe_name),
                                    color::colorize_coord(&row.coordinate()),
                                    if let Some(ri) = remote_probe_idx {
                                        color::colorize_probe(*ri, &remote_probe_name).to_string()
                                    } else {
                                        remote_probe_name
                                    },
                                    lc.epoch.0,
                                    lc.ticks.0
                                );
                                count += 1;
                            }
                            if l.verbose != 0 {
                                println!();
                            }
                        }
                        _ => {
                            count += 1;
                        }
                    }
                } else {
                    break 'inner;
                }
            }
        }
        if count == init_count {
            break 'outer;
        }
    }
    Ok(())
}

fn print_event_info(
    idx: usize,
    ev: ReportLogEntry,
    eid: &EventId,
    payload: Option<u32>,
    l: &Log,
    cfg: &Cfg,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(ref fmt) = l.format {
        println!("{}", format::format(cfg, &ev, fmt));
    } else {
        let event_meta = meta::get_event_meta(&cfg, &ev.probe_id, eid);
        let probe_meta = cfg.probes.get(&ev.probe_id.get_raw());
        let pname = probe_meta
            .map(|pm| pm.name.clone())
            .unwrap_or_else(|| ev.probe_id.get_raw().to_string());
        let ename = event_meta
            .as_ref()
            .map(|em| em.name.clone())
            .unwrap_or_else(|_| eid.get_raw().to_string());
        if let Some(pl) = payload {
            if let Some(msg) = event_meta.as_ref().ok().and_then(|e| {
                if e.description.contains_formatting() {
                    e.description.format_payload(&pl).ok()
                } else {
                    None
                }
            }) {
                println!(
                    "{} {}: {}",
                    color::colorize_probe(idx, &pname.to_string()),
                    color::colorize_coord(&ev.coordinate()),
                    color::white(&msg)
                );
            } else {
                println!(
                    "{} {} {}",
                    ename,
                    color::colorize_probe(idx, &pname.to_string()),
                    color::colorize_coord(&ev.coordinate())
                );
            }
        } else {
            println!(
                "{} {} {}",
                ename,
                color::colorize_probe(idx, &pname.to_string()),
                color::colorize_coord(&ev.coordinate())
            );
        }

        if l.verbose != 0 && event_meta.is_ok() {
            let emeta = event_meta.expect("just checked that event meta is_ok");
            println!(
                "    {}",
                color::colorize_info(
                    "description",
                    if !emeta.description.is_empty() {
                        &emeta.description
                    } else {
                        "None"
                    }
                )
            );
            println!(
                "    {}",
                color::colorize_info(
                    "payload",
                    if let Some(ref p) =
                        meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), payload)?
                    {
                        p
                    } else {
                        "None"
                    }
                )
            );
            println!(
                "    {}",
                color::colorize_info("tags", &emeta.tags.replace(";", ", "))
            );
            println!(
                "    {}",
                match (emeta.file.is_empty(), emeta.line.is_empty()) {
                    (false, false) => {
                        color::colorize_info(
                            "source",
                            &format!("\"{}#L{}\"", emeta.file, emeta.line),
                        )
                    }
                    (true, false) => {
                        color::colorize_info("source", &format!("\"{}\"", emeta.file))
                    }
                    _ => {
                        color::colorize_info("source", "None")
                    }
                }
            );
        }
        if l.verbose > 1 && probe_meta.is_some() {
            let pmeta = probe_meta.expect("just checked that probe meta is_some");
            println!(
                "    {}",
                color::colorize_info("probe tags", &pmeta.tags.replace(";", ", "))
            );
            println!(
                "    {}",
                match (pmeta.file.is_empty(), pmeta.line.is_empty()) {
                    (false, false) => {
                        color::colorize_info(
                            "probe source",
                            &format!("\"{}#L{}\"", pmeta.file, pmeta.line),
                        )
                    }
                    (false, true) => {
                        color::colorize_info("probe source", &format!("\"{}\"", pmeta.file))
                    }
                    _ => color::colorize_info("probe source", "None"),
                }
            );
            let comp_name_or_id =
                if let Some(n) = cfg.component_names.get(&pmeta.component_id.to_string()) {
                    n.to_string()
                } else {
                    pmeta.component_id.to_string()
                };
            println!(
                "    {}",
                color::colorize_info("component", &comp_name_or_id)
            );
        }
        if l.verbose != 0 {
            println!();
        }
    }
    Ok(())
}
