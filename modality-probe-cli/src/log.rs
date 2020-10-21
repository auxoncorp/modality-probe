use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    fs::File,
    path::PathBuf,
};

use structopt::StructOpt;

use modality_probe::{LogicalClock, ProbeId};
use modality_probe_collector_common::{json, LogEntryData, ReportLogEntry};

use crate::{
    hopefully, hopefully_ok,
    meta::{self, Cfg, EventMeta},
};

// 3 empty columns between each timeline.
const COL_SPACE: &str = "   ";
const COL_EDGE: &str = "---";

/// View the trace as a log.
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
    /// Print the log as an ASCII-art graph.
    #[structopt(long)]
    pub graph: bool,
    /// Provide (more) verbose output.
    /// (-v, -vv, -vvv, &c.)
    #[structopt(short, parse(from_occurrences))]
    pub verbose: u8,
}

pub fn run(l: Log) -> Result<(), Box<dyn std::error::Error>> {
    if l.probe.is_some() {
        probe_log(l)
    } else {
        log_all(l)
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
        if !ev.is_internal_event() {
            p.push(ev);
        }
    }

    // Sort the probe-sorted events by sequence.
    let mut clock_rows = Vec::new();
    for plog in probes.values_mut() {
        plog.sort_by_key(|p| std::cmp::Reverse((p.sequence_number, p.sequence_index)));
        for r in plog.iter() {
            if let LogEntryData::TraceClock(_) = r.data {
                clock_rows.push(r.clone());
            }
        }
    }

    if l.graph {
        print_as_graph(probes, clock_rows, &cfg)
    } else {
        print_as_log(probes, &l, &cfg)
    }
}

fn print_as_graph(
    mut probes: HashMap<ProbeId, Vec<ReportLogEntry>>,
    clock_rows: Vec<ReportLogEntry>,
    cfg: &Cfg,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut pending_targets: HashMap<_, (usize, ProbeId)> = HashMap::new();
    let mut pending_sources = HashMap::new();
    let mut count = 0;
    let mut blocked_tls: HashSet<ProbeId> = HashSet::new();
    let n_probes = probes.len();

    loop {
        let init_count = count;
        for (idx, (probe_id, log)) in probes.iter_mut().enumerate() {
            if let Some(row) = log.pop() {
                match row.data {
                    LogEntryData::Event(id) => {
                        if blocked_tls.get(probe_id).is_none() {
                            let emeta = meta::get_event_meta(&cfg, &probe_id, &id)?;
                            let pmeta = hopefully_ok!(
                                cfg.probes.get(&probe_id.get_raw()),
                                "Couldn't find probe"
                            )?;
                            print_event_row(
                                &format!("{} @ {} ({})", emeta.name, pmeta.name, row.coordinate(),),
                                idx,
                                n_probes,
                            )?;
                            print_info_row(
                                n_probes,
                                &format!("description: \"{}\"", emeta.description),
                            )?;
                            print_info_row(
                                n_probes,
                                &format!("tags: {}", emeta.tags.replace(";", ", ")),
                            )?;
                            if !emeta.file.is_empty() && !emeta.line.is_empty() {
                                print_info_row(
                                    n_probes,
                                    &format!("source: \"{}#L{}\"", emeta.file, emeta.line),
                                )?;
                            }
                            print_info_row(n_probes, "")?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::EventWithPayload(id, pl) => {
                        if blocked_tls.get(probe_id).is_none() {
                            let emeta = meta::get_event_meta(&cfg, &probe_id, &id)?;
                            let pmeta = hopefully_ok!(
                                cfg.probes.get(&probe_id.get_raw()),
                                "couldn't find probe"
                            )?;
                            print_event_row(
                                &format!("{} @ {} ({})", emeta.name, pmeta.name, row.coordinate(),),
                                idx,
                                n_probes,
                            )?;
                            if let Some(pp) = meta::parsed_payload(
                                emeta.type_hint.as_ref().map(|s| s.as_ref()),
                                Some(pl),
                            )? {
                                print_info_row(n_probes, &format!("payload: {}", pp))?;
                            }
                            print_info_row(
                                n_probes,
                                &format!("tags: {}", emeta.tags.replace(";", ", ")),
                            )?;
                            if !emeta.file.is_empty() && !emeta.line.is_empty() {
                                print_info_row(
                                    n_probes,
                                    &format!("source: \"{}#L{}\"", emeta.file, emeta.line),
                                )?;
                            }
                            print_info_row(n_probes, "")?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::TraceClock(lc) => {
                        // This is a local clock.
                        let (lc_id, clock) = lc.pack();
                        if lc.id == *probe_id {
                            // The self clock 0 is useful from a
                            // causal standpoint, but from a
                            // coordinating-timelines standpoint, it's
                            // ambiguous because it appears whether or
                            // not a snapshot was produced or merged.
                            if clock != 0 {
                                if let Some(next) = log.pop() {
                                    match next.data.trace_clock() {
                                        Some(next_lc) => {
                                            if next_lc.id == *probe_id {
                                                handle_source_edge(
                                                    &pending_targets,
                                                    &mut pending_sources,
                                                    cfg,
                                                    lc_id,
                                                    clock,
                                                    probe_id,
                                                    n_probes,
                                                    &clock_rows,
                                                    &mut blocked_tls,
                                                    idx,
                                                    lc,
                                                )?;
                                            }
                                        }
                                        None => {
                                            handle_source_edge(
                                                &pending_targets,
                                                &mut pending_sources,
                                                cfg,
                                                lc_id,
                                                clock,
                                                probe_id,
                                                n_probes,
                                                &clock_rows,
                                                &mut blocked_tls,
                                                idx,
                                                lc,
                                            )?;
                                        }
                                    }
                                    log.push(next);
                                } else {
                                    handle_source_edge(
                                        &pending_targets,
                                        &mut pending_sources,
                                        cfg,
                                        lc_id,
                                        clock,
                                        probe_id,
                                        n_probes,
                                        &clock_rows,
                                        &mut blocked_tls,
                                        idx,
                                        lc,
                                    )?;
                                }
                            }
                        // This is a foreign clock: `lc.id != probe_id`.
                        } else {
                            let (lc_id, clock) = lc.pack();
                            if let Some(source_idx) = pending_sources.get(&(lc_id, clock + 1)) {
                                let from_pm = hopefully_ok!(
                                    cfg.probes.get(&lc_id.get_raw()),
                                    format!("probe {} could not be found", lc_id.get_raw())
                                )?;
                                let to_pm = hopefully_ok!(
                                    cfg.probes.get(&probe_id.get_raw()),
                                    format!("probe {} could not be found", probe_id.get_raw())
                                )?;
                                print_edge_line(
                                    *source_idx,
                                    idx,
                                    &from_pm.name,
                                    &to_pm.name,
                                    n_probes,
                                )?;
                                print_info_row(n_probes, "")?;
                                blocked_tls.remove(probe_id);
                                blocked_tls.remove(&lc.id);
                            // There is not a source waiting to be
                            // matched with this target.
                            } else {
                                let is_present = clock_rows.iter().any(|r| {
                                    let (inner_lc_id, inner_clock) =
                                        r.data.trace_clock().unwrap().pack();
                                    r.probe_id == inner_lc_id
                                        && (lc_id, clock + 1) == (inner_lc_id, inner_clock)
                                });
                                if is_present {
                                    pending_targets.insert((lc_id, clock), (idx, *probe_id));
                                    blocked_tls.insert(*probe_id);
                                }
                            }
                        }
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

#[allow(clippy::too_many_arguments)]
fn handle_source_edge(
    pending_targets: &HashMap<(ProbeId, u32), (usize, ProbeId)>,
    pending_sources: &mut HashMap<(ProbeId, u32), usize>,
    cfg: &Cfg,
    lc_id: ProbeId,
    clock: u32,
    probe_id: &ProbeId,
    n_probes: usize,
    clock_rows: &[ReportLogEntry],
    blocked_tls: &mut HashSet<ProbeId>,
    idx: usize,
    lc: LogicalClock,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some((target_idx, target_id)) = pending_targets.get(&(lc_id, clock - 1)) {
        let from_pm = hopefully_ok!(
            cfg.probes.get(&probe_id.get_raw()),
            format!("probe {} could not be found", probe_id.get_raw())
        )?;
        let to_pm = hopefully_ok!(
            cfg.probes.get(&target_id.get_raw()),
            format!("probe {} could not be found", lc_id.get_raw())
        )?;
        print_edge_line(idx, *target_idx, &from_pm.name, &to_pm.name, n_probes)?;
        print_info_row(n_probes, "")?;
        blocked_tls.remove(probe_id);
        blocked_tls.remove(&target_id);
    } else {
        let is_present = clock_rows.iter().any(|r| {
            r.probe_id != *probe_id && r.data.trace_clock().unwrap().pack() == (lc_id, clock - 1)
        });
        if is_present {
            let (lc_id, clock) = lc.pack();
            pending_sources.insert((lc_id, clock), idx);
            blocked_tls.insert(*probe_id);
        }
    }
    Ok(())
}

fn print_event_row(
    name: &str,
    idx: usize,
    n_probe: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        if i == idx {
            hopefully!(write!(s, "*{}", COL_SPACE), "graph formatting failure")?;
        } else {
            hopefully!(write!(s, "|{}", COL_SPACE), "graph formatting failure")?;
        }
    }
    hopefully!(write!(s, "{}", name), "graph formatting failure")?;
    println!("{}", s);
    Ok(())
}

fn print_info_row(n_probe: usize, info: &str) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for _ in 0..n_probe {
        hopefully!(write!(s, "|{}", COL_SPACE), "graph formatting failure")?;
    }
    hopefully!(write!(s, "    {}", info), "graph formatting failure")?;
    println!("{}", s);
    Ok(())
}

fn print_edge_line(
    from: usize,
    to: usize,
    from_pname: &str,
    to_pname: &str,
    n_probes: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    // comments about what's happening here.
    let mut s = String::new();
    let l_to_r = from < to;
    for i in 0..n_probes {
        // in an left-to-right edge, this is the source timeline and
        // the adjacent timeline is the target.
        // It's a special case because we must adjust for the arrow's
        // head.
        if l_to_r && i == from && i == to - 1 {
            hopefully!(
                write!(s, "+{}>", &COL_EDGE[1..]),
                "internal error formatting graph"
            )?;
        // This timeline is the source (left-to-right).
        } else if l_to_r && i == from {
            hopefully!(
                write!(s, "+{}", COL_EDGE),
                "internal error formatting graph"
            )?;
        // This timeline is the source (right-to-left).
        } else if i == from {
            hopefully!(
                write!(s, "+{}", COL_SPACE),
                "internal error formatting graph"
            )?;
        // This timeline is the target (in left-to-right).
        } else if l_to_r && i == to {
            hopefully!(
                write!(s, "+{}", COL_SPACE),
                "internal error formatting graph"
            )?;
        // This timeline is the target (in right-to-left).
        } else if i == to {
            hopefully!(
                write!(s, "+<{}", &COL_EDGE[1..]),
                "internal error formatting graph"
            )?;
        // In a left-to-right edge, write the head of the arrow.
        } else if l_to_r && i == to - 1 {
            hopefully!(
                write!(s, "{}>", COL_EDGE),
                "internal error formatting graph"
            )?;
        // We're on a timeline that lay between the source and
        // target and the edge should “jump” it.
        } else if (l_to_r && i > from && i < to) || (i > to && i < from) {
            hopefully!(
                write!(s, "-{}", COL_EDGE),
                "internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "|{}", COL_SPACE),
                "internal error formatting graph"
            )?;
        }
    }

    hopefully!(
        write!(s, "{} merged a snapshot from {}", to_pname, from_pname),
        "graph formatting error"
    )?;
    println!("{}", s);
    Ok(())
}

fn print_as_log(
    mut probes: HashMap<ProbeId, Vec<ReportLogEntry>>,
    l: &Log,
    cfg: &Cfg,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut count = 0;
    'outer: loop {
        let init_count = count;
        for (probe_id, log) in probes.iter_mut() {
            let mut seen_self_clock = false;
            'inner: loop {
                if let Some(row) = log.pop() {
                    match row.data {
                        LogEntryData::Event(id) => {
                            let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                            print_event_info(row, emeta, None, &probe_name, l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::EventWithPayload(id, pl) => {
                            let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                            print_event_info(row, emeta, Some(pl), &probe_name, l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::TraceClock(lc) => {
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                            if lc.id == *probe_id {
                                if !seen_self_clock {
                                    if l.verbose == 0 {
                                        println!();
                                    }
                                    println!(
                                        "Clock Tick @ {} ({}) clock=({}, {})",
                                        probe_name,
                                        row.coordinate(),
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
                                    .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                                println!(
                                    "Snapshot Merge @ {} ({}), from={} clock=({}, {})",
                                    probe_name,
                                    row.coordinate(),
                                    remote_probe_name,
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

fn probe_log(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let p = l.probe.as_ref().unwrap();
    let cfg = meta::assemble_components(&mut l.components)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("failed to open the report file at {}", l.report.display())
    )?;

    let probe = match cfg.probes.iter().find(|(_, v)| v.name == *p) {
        Some((_, pm)) => pm,
        None => {
            let pid = hopefully!(p.parse::<u32>(), format!("probe {} could not be found", p))?;
            hopefully_ok!(
                cfg.probes.get(&pid),
                format!("probe {} could not be found", p)
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

    for row in log {
        match row.data {
            LogEntryData::Event(id) => {
                let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                let probe_name = cfg
                    .probes
                    .get(&row.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                print_event_info(row, emeta, None, &probe_name, &l, &cfg)?;
            }
            LogEntryData::EventWithPayload(id, pl) => {
                let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                let probe_name = cfg
                    .probes
                    .get(&row.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                print_event_info(row, emeta, Some(pl), &probe_name, &l, &cfg)?;
            }
            LogEntryData::TraceClock(lc) => {
                let probe_name = cfg
                    .probes
                    .get(&row.probe_id.get_raw())
                    .map(|p| p.name.clone())
                    .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                if lc.id == row.probe_id {
                    if l.verbose == 0 {
                        println!();
                    }
                    println!(
                        "Clock Tick @ {} ({}) clock=({}, {})",
                        probe_name,
                        row.coordinate(),
                        lc.epoch.0,
                        lc.ticks.0
                    );
                } else {
                    let remote_probe_name = cfg
                        .probes
                        .get(&row.probe_id.get_raw())
                        .map(|p| p.name.clone())
                        .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                    println!(
                        "Snapshot Merge @ {} ({}), from={} clock=({}, {})",
                        probe_name,
                        row.coordinate(),
                        remote_probe_name,
                        lc.epoch.0,
                        lc.ticks.0
                    );
                }
            }
            _ => (),
        }
    }
    Ok(())
}

fn print_event_info(
    ev: ReportLogEntry,
    def: &EventMeta,
    payload: Option<u32>,
    pname: &str,
    l: &Log,
    cfg: &Cfg,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("{} @ {} ({})", def.name, pname, ev.coordinate());
    if l.verbose != 0 {
        println!(
            "    description: \"{}\"",
            if !def.description.is_empty() {
                &def.description
            } else {
                "None"
            }
        );
        println!(
            "    payload: {}",
            if let Some(p) =
                meta::parsed_payload(def.type_hint.as_ref().map(|s| s.as_ref()), payload)?
            {
                p
            } else {
                "None".to_string()
            }
        );
        println!("    tags: {}", def.tags.replace(";", ", "));
        println!(
            "{}",
            match (def.file.is_empty(), def.line.is_empty()) {
                (false, false) => {
                    format!("    source: \"{}#L{}\"", def.file, def.line)
                }
                (true, false) => {
                    format!("    source: \"{}\"", def.file)
                }
                _ => "    source: None".to_string(),
            }
        );
    }
    if l.verbose > 1 {
        if let Some(pmeta) = cfg.probes.get(&ev.probe_id.get_raw()) {
            println!("    probe tags: {}", pmeta.tags.replace(";", ", "));
            println!(
                "{}",
                match (pmeta.file.is_empty(), pmeta.line.is_empty()) {
                    (false, false) => {
                        format!("    probe source: \"{}#L{}\"", pmeta.file, pmeta.line)
                    }
                    (false, true) => {
                        format!("    probe source: \"{}\"", pmeta.file)
                    }
                    _ => "    probe source: None".to_string(),
                }
            );
            let comp_name_or_id =
                if let Some(n) = cfg.component_names.get(&pmeta.component_id.to_string()) {
                    n.to_string()
                } else {
                    pmeta.component_id.to_string()
                };
            println!("    component: {}", comp_name_or_id);
        }
    }
    if l.verbose != 0 {
        println!();
    }
    Ok(())
}
