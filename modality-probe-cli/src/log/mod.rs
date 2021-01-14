use std::{
    collections::{BTreeMap, HashMap},
    convert::TryFrom,
    fs::File,
    path::PathBuf,
};

use structopt::StructOpt;

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{json, LogEntryData, ReportLogEntry};

use crate::{
    description_format::DescriptionFormat,
    hopefully, hopefully_ok,
    meta::{self, Cfg, MetaMeter},
};

pub mod color;
pub mod format;
pub mod graph;
pub mod radius;

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
    /// |    %pi    | Probe id           |
    /// |    %pn    | Probe name         |
    /// |    %pd    | Probe description  |
    /// |    %pf    | Probe file         |
    /// |    %pl    | Probe line         |
    /// |    %pt    | Probe tags         |
    /// |    %ci    | Component id       |
    /// |    %cn    | Component name     |
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

type SortedProbes = (
    BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    Vec<(ProbeId, LogicalClock)>,
);

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
                LogEntryData::TraceClock(clock) => clock_rows.push((r.probe_id, clock)),
                LogEntryData::TraceClockWithTime(_, clock) => clock_rows.push((r.probe_id, clock)),
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
    cfg: &dyn MetaMeter,
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
                            print_event_info(
                                idx,
                                probe_id,
                                &row.coordinate(),
                                &id,
                                None,
                                &l.format,
                                l.verbose,
                                cfg,
                            )?;
                            count += 1;
                        }
                        LogEntryData::EventWithPayload(id, pl)
                        | LogEntryData::EventWithPayloadWithTime(.., id, pl) => {
                            print_event_info(
                                idx,
                                probe_id,
                                &row.coordinate(),
                                &id,
                                Some(pl),
                                &l.format,
                                l.verbose,
                                cfg,
                            )?;
                            count += 1;
                        }
                        LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
                            let probe_name = cfg
                                .probe_name(probe_id)
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
                                    .probe_name(&lc.id)
                                    .unwrap_or_else(|| lc.id.get_raw().to_string());
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

#[allow(clippy::too_many_arguments)]
pub fn print_event_info(
    idx: usize,
    probe_id: &ProbeId,
    coord: &str,
    eid: &EventId,
    payload: Option<u32>,
    format: &Option<String>,
    verbosity: u8,
    cfg: &dyn MetaMeter,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(ref fmt) = format {
        println!(
            "{}",
            format::format(
                cfg,
                format::Context {
                    probe_id: *probe_id,
                    event_id: *eid,
                    user_coordinate: coord.to_string(),
                    payload
                },
                fmt
            )
        );
    } else {
        let pname = cfg
            .probe_name(&probe_id)
            .unwrap_or_else(|| probe_id.get_raw().to_string());
        let ename = cfg
            .event_name(&probe_id, eid)
            .unwrap_or_else(|| probe_id.get_raw().to_string());
        if let Some(pl) = payload {
            if let Some(msg) = cfg
                .event_description(&probe_id, eid)
                .map(|desc| {
                    if desc.contains_formatting() {
                        desc.format_payload(&pl).ok()
                    } else {
                        None
                    }
                })
                .flatten()
            {
                println!(
                    "{} {}: {}",
                    color::colorize_probe(idx, &pname),
                    color::colorize_coord(coord),
                    color::white(&msg)
                );
            } else {
                println!(
                    "{} {} {}",
                    ename,
                    color::colorize_probe(idx, &pname),
                    color::colorize_coord(coord)
                );
            }
        } else {
            println!(
                "{} {} {}",
                ename,
                color::colorize_probe(idx, &pname),
                color::colorize_coord(coord)
            );
        }

        if verbosity != 0 {
            if let Some(desc) = cfg.event_description(&probe_id, eid) {
                println!(
                    "    {}",
                    color::colorize_info(
                        "description",
                        if !desc.is_empty() { &desc } else { "None" }
                    )
                );
            }
            println!(
                "    {}",
                color::colorize_info(
                    "payload",
                    if let Some(ref p) = meta::parsed_payload(
                        cfg.event_type_hint(&probe_id, eid)
                            .as_ref()
                            .map(|s| s.as_ref()),
                        payload
                    )? {
                        p
                    } else {
                        "None"
                    }
                )
            );
            println!(
                "    {}",
                color::colorize_info(
                    "tags",
                    &cfg.event_tags(&probe_id, eid)
                        .map(|tags| tags.join(", "))
                        .unwrap_or_else(|| "None".to_string())
                )
            );
            if cfg.event_file(&probe_id, eid).is_some() && cfg.event_line(&probe_id, eid).is_some()
            {
                let file = cfg.event_file(&probe_id, eid).unwrap();
                let line = cfg.event_line(&probe_id, eid).unwrap();
                let out = match (file.is_empty(), line.is_empty()) {
                    (false, false) => {
                        color::colorize_info("source", &format!("\"{}#L{}\"", file, line))
                    }
                    (true, false) => color::colorize_info("source", &format!("\"{}\"", file)),
                    _ => color::colorize_info("source", "None"),
                };
                println!("    {}", out);
            }
        }
        if verbosity > 1 {
            println!(
                "    {}",
                color::colorize_info(
                    "probe tags",
                    &cfg.probe_tags(&probe_id)
                        .map(|tags| tags.join(", "))
                        .unwrap_or_else(String::new)
                )
            );
            if cfg.probe_file(&probe_id).is_some() && cfg.probe_line(&probe_id).is_some() {
                let file = cfg.probe_file(&probe_id).unwrap();
                let line = cfg.probe_line(&probe_id).unwrap();
                let out = match (file.is_empty(), line.is_empty()) {
                    (false, false) => {
                        color::colorize_info("probe source", &format!("\"{}#L{}\"", file, line))
                    }
                    (false, true) => color::colorize_info("probe source", &format!("\"{}\"", file)),
                    _ => color::colorize_info("probe source", "None"),
                };
                println!("    {}", out);
            }
            if let Some(comp_name_or_id) = cfg
                .probe_component_name(&probe_id)
                .or_else(|| cfg.probe_component_id(&probe_id).map(|id| id.to_string()))
            {
                println!(
                    "    {}",
                    color::colorize_info("component", &comp_name_or_id)
                );
            }
        }
        if verbosity != 0 {
            println!();
        }
    }
    Ok(())
}
