use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Write,
    fs::File,
    io::Write as WriteIo,
    path::PathBuf,
};

use structopt::StructOpt;

use modality_probe::{LogicalClock, ProbeId};
use modality_probe_collector_common::{json, LogEntryData, ReportLogEntry};

use crate::{
    hopefully, hopefully_ok,
    meta::{self, Cfg, EventMeta, ProbeMeta},
};

// 3 empty columns between each timeline.
const COL_SPACE: &str = "   ";
const COL_EDGE: &str = "---";

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
}

pub fn run(mut l: Log) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut l.component_path)?;
    let mut log_file = hopefully!(
        File::open(&l.report),
        format!("Failed to open the report file at {}", l.report.display())
    )?;

    let report = json::read_log_entries(&mut log_file)?;
    let (probes, clock_rows) = sort_probes(&cfg, &l, report)?;

    if l.graph {
        print_as_graph(probes, clock_rows, &cfg, &l, std::io::stdout())
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
    Ok((probes, clock_rows))
}

fn print_as_graph<W: WriteIo>(
    mut probes: BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    clock_rows: Vec<ReportLogEntry>,
    cfg: &Cfg,
    l: &Log,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    // Edges waiting to be drawn.
    let mut pending_targets: HashMap<_, (usize, ProbeId)> = HashMap::new();
    let mut pending_sources = HashMap::new();

    // Our “watch dog”. This ticks while the outer loop is
    // productive. If it stops ticking, we're done.
    let mut count = 0;

    // The timelines that are currently blocked and waiting the other
    // end of an egde to show up.
    let mut blocked_tls: HashSet<ProbeId> = HashSet::new();

    // How many timelines are there?
    let n_probes = probes.len();

    loop {
        let init_count = count;
        for (idx, (probe_id, log)) in probes.iter_mut().enumerate() {
            if let Some(row) = log.pop() {
                match row.data {
                    LogEntryData::Event(id) | LogEntryData::EventWithTime(.., id) => {
                        if blocked_tls.get(probe_id).is_none() {
                            let emeta = meta::get_event_meta(&cfg, &probe_id, &id)?;
                            let pmeta = hopefully_ok!(
                                cfg.probes.get(&probe_id.get_raw()),
                                "Couldn't find probe"
                            )?;
                            print_event_row(
                                &format!("{} @ {} ({})", emeta.name, pmeta.name, row.coordinate()),
                                idx,
                                n_probes,
                                &mut stream,
                            )?;

                            handle_graph_verbosity(
                                l,
                                n_probes,
                                emeta,
                                pmeta,
                                None,
                                cfg,
                                &mut stream,
                            )?;

                            print_info_row(n_probes, "", &mut stream)?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::EventWithPayload(id, pl)
                    | LogEntryData::EventWithPayloadWithTime(.., id, pl) => {
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
                                &mut stream,
                            )?;

                            handle_graph_verbosity(
                                l,
                                n_probes,
                                emeta,
                                pmeta,
                                Some(pl),
                                cfg,
                                &mut stream,
                            )?;

                            print_info_row(n_probes, "", &mut stream)?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
                        // This is a local clock.
                        let (lc_id, clock) = lc.pack();
                        if lc.id == *probe_id {
                            // The self-clock `0` is useful from a
                            // causal standpoint, but from a
                            // coordinating-timelines standpoint, it's
                            // ambiguous because it appears whether a
                            // snapshot was produced or not.
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
                                                    &mut stream,
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
                                                &mut stream,
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
                                        &mut stream,
                                    )?;
                                }
                            }
                        // This is a foreign clock: `lc.id != probe_id`.
                        } else {
                            let (lc_id, clock) = lc.pack();
                            let from_pm = hopefully_ok!(
                                cfg.probes.get(&lc_id.get_raw()),
                                format!("Probe {} could not be found", lc_id.get_raw())
                            )?;
                            let to_pm = hopefully_ok!(
                                cfg.probes.get(&probe_id.get_raw()),
                                format!("Probe {} could not be found", probe_id.get_raw())
                            )?;
                            if let Some(source_idx) = pending_sources.get(&(lc_id, clock + 1)) {
                                print_edge_line(
                                    *source_idx,
                                    idx,
                                    &from_pm.name,
                                    &to_pm.name,
                                    n_probes,
                                    &mut stream,
                                )?;
                                print_info_row(n_probes, "", &mut stream)?;
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
                                } else {
                                    print_missing_edge_line(
                                        idx,
                                        &from_pm.name,
                                        &to_pm.name,
                                        n_probes,
                                        l.probe.is_some(),
                                        &mut stream,
                                    )?;
                                    print_info_row(n_probes, "", &mut stream)?;
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

fn handle_graph_verbosity<W: WriteIo>(
    l: &Log,
    n_probes: usize,
    emeta: &EventMeta,
    pmeta: &ProbeMeta,
    pl: Option<u32>,
    cfg: &Cfg,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    if l.verbose != 0 {
        print_info_row(
            n_probes,
            &format!("description: \"{}\"", emeta.description),
            &mut stream,
        )?;
        // TODO(dan@auxon.io): Interpolate log-style payload / string
        // combos here if they're present.
        // https://github.com/auxoncorp/modality-probe/issues/281
        if let Some(pp) = meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), pl)? {
            print_info_row(n_probes, &format!("payload: {}", pp), &mut stream)?;
        }
        print_info_row(
            n_probes,
            &format!("tags: {}", emeta.tags.replace(";", ", ")),
            &mut stream,
        )?;
        if !emeta.file.is_empty() && !emeta.line.is_empty() {
            print_info_row(
                n_probes,
                &format!("source: \"{}#L{}\"", emeta.file, emeta.line),
                &mut stream,
            )?;
        }
    }
    if l.verbose > 1 {
        print_info_row(
            n_probes,
            &format!("probe_tags: {}", pmeta.tags.replace(";", ", ")),
            &mut stream,
        )?;
        print_info_row(
            n_probes,
            &match (pmeta.file.is_empty(), pmeta.line.is_empty()) {
                (false, false) => format!("probe source: \"{}#L{}\"", pmeta.file, pmeta.line),
                (false, true) => format!("probe source: \"{}\"", pmeta.file),
                _ => "probe source: None".to_string(),
            },
            &mut stream,
        )?;
        let comp_name_or_id =
            if let Some(n) = cfg.component_names.get(&pmeta.component_id.to_string()) {
                n.to_string()
            } else {
                pmeta.component_id.to_string()
            };
        print_info_row(
            n_probes,
            &format!("component: {}", comp_name_or_id),
            &mut stream,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn handle_source_edge<W: WriteIo>(
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
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some((target_idx, target_id)) = pending_targets.get(&(lc_id, clock - 1)) {
        let from_pm = hopefully_ok!(
            cfg.probes.get(&probe_id.get_raw()),
            format!("Probe {} could not be found", probe_id.get_raw())
        )?;
        let to_pm = hopefully_ok!(
            cfg.probes.get(&target_id.get_raw()),
            format!("Probe {} could not be found", lc_id.get_raw())
        )?;
        print_edge_line(
            idx,
            *target_idx,
            &from_pm.name,
            &to_pm.name,
            n_probes,
            &mut stream,
        )?;
        print_info_row(n_probes, "", &mut stream)?;
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

fn print_event_row<W: WriteIo>(
    name: &str,
    idx: usize,
    n_probe: usize,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        if i == idx {
            hopefully!(
                write!(s, "*{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "|{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(write!(s, "{}", name), "Internal error formatting graph")?;
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

fn print_info_row<W: WriteIo>(
    n_probe: usize,
    info: &str,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        // If the info string is empty and we're on the lat timeline,
        // don't include the column spacing.
        if i == n_probe.saturating_sub(1) && info.is_empty() {
            hopefully!(write!(s, "|"), "Internal error formatting graph")?;
        } else {
            hopefully!(
                write!(s, "|{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    if !info.is_empty() {
        hopefully!(write!(s, "    {}", info), "Internal error formatting graph")?;
    }
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

fn print_edge_line<W: WriteIo>(
    from: usize,
    to: usize,
    from_pname: &str,
    to_pname: &str,
    n_probes: usize,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    let l_to_r = from < to;
    for i in 0..n_probes {
        // In a left-to-right edge, this is the source timeline and
        // the right-adjacent timeline is the target. It's a special
        // case because we must adjust for the arrow's head.
        if l_to_r && i == from && i == to - 1 {
            hopefully!(
                write!(s, "+{}>", &COL_EDGE[1..]),
                "Internal error formatting graph"
            )?;
        // This timeline is the source (left-to-right).
        } else if l_to_r && i == from {
            hopefully!(
                write!(s, "+{}", COL_EDGE),
                "Internal error formatting graph"
            )?;
        // This timeline is the source (right-to-left).
        } else if i == from {
            hopefully!(
                write!(s, "+{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        // This timeline is the target (in left-to-right).
        } else if l_to_r && i == to {
            hopefully!(
                write!(s, "+{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        // This timeline is the target (in right-to-left).
        } else if i == to {
            hopefully!(
                write!(s, "+<{}", &COL_EDGE[1..]),
                "Internal error formatting graph"
            )?;
        // In a left-to-right edge, write the head of the arrow.
        } else if l_to_r && i == to - 1 {
            hopefully!(
                write!(s, "{}>", COL_EDGE),
                "Internal error formatting graph"
            )?;
        // We're on a timeline that lay between the source and
        // target and the edge should “jump” it.
        } else if (l_to_r && i > from && i < to) || (i > to && i < from) {
            hopefully!(
                write!(s, "-{}", COL_EDGE),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "|{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(
        write!(s, "{} merged a snapshot from {}", to_pname, from_pname),
        "Internal error formatting graph"
    )?;
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

fn print_missing_edge_line<W: WriteIo>(
    idx: usize,
    from_name: &str,
    to_name: &str,
    n_probe: usize,
    single_probe_mode: bool,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        if i == idx && !single_probe_mode {
            hopefully!(
                write!(s, "?{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        } else if i == idx && single_probe_mode {
            hopefully!(
                write!(s, "+<-{}", &COL_SPACE[2..]),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "|{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(
        if single_probe_mode {
            write!(s, "{} merged a snapshot from {}", to_name, from_name)
        } else {
            write!(
                s,
                "{} expected a snapshot from {} but it is missing",
                to_name, from_name
            )
        },
        "Internal error formatting graph"
    )?;
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

fn print_as_log(
    mut probes: BTreeMap<ProbeId, Vec<ReportLogEntry>>,
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
                        LogEntryData::Event(id) | LogEntryData::EventWithTime(.., id) => {
                            let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                            print_event_info(row, emeta, None, &probe_name, l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::EventWithPayload(id, pl)
                        | LogEntryData::EventWithPayloadWithTime(.., id, pl) => {
                            let emeta = meta::get_event_meta(&cfg, &row.probe_id, &id)?;
                            let probe_name = cfg
                                .probes
                                .get(&row.probe_id.get_raw())
                                .map(|p| p.name.clone())
                                .unwrap_or(format!("UNKNOWN_PROBE_{}", row.probe_id.get_raw()));
                            print_event_info(row, emeta, Some(pl), &probe_name, l, &cfg)?;
                            count += 1;
                        }
                        LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
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

#[cfg(test)]
mod test {
    use chrono::Utc;
    use uuid::Uuid;

    use modality_probe::{EventId, NanosecondResolution, ProbeEpoch, ProbeTicks, WallClockId};
    use modality_probe_collector_common::{SequenceNumber, SessionId};

    use crate::meta::{Cfg, EventMeta, ProbeMeta};

    use super::*;

    fn cfg() -> Cfg {
        let a_uuid = Uuid::new_v4();
        Cfg {
            probes: vec![
                (
                    1,
                    ProbeMeta {
                        component_id: a_uuid,
                        id: 1,
                        name: "one".to_string(),
                        description: "one".to_string(),
                        file: "one.c".to_string(),
                        line: "1".to_string(),
                        tags: "".to_string(),
                    },
                ),
                (
                    2,
                    ProbeMeta {
                        component_id: a_uuid,
                        id: 2,
                        name: "two".to_string(),
                        description: "two".to_string(),
                        file: "two.c".to_string(),
                        line: "2".to_string(),
                        tags: "".to_string(),
                    },
                ),
                (
                    3,
                    ProbeMeta {
                        component_id: a_uuid,
                        id: 3,
                        name: "three".to_string(),
                        description: "three".to_string(),
                        file: "three.c".to_string(),
                        line: "3".to_string(),
                        tags: "".to_string(),
                    },
                ),
                (
                    4,
                    ProbeMeta {
                        component_id: a_uuid,
                        id: 4,
                        name: "four".to_string(),
                        description: "four".to_string(),
                        file: "four.c".to_string(),
                        line: "4".to_string(),
                        tags: "".to_string(),
                    },
                ),
            ]
            .into_iter()
            .collect(),
            events: vec![
                (
                    (a_uuid, 1),
                    EventMeta {
                        component_id: a_uuid,
                        id: 1,
                        name: "one".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        description: "one".to_string(),
                        file: "one.c".to_string(),
                        line: "1".to_string(),
                    },
                ),
                (
                    (a_uuid, 2),
                    EventMeta {
                        component_id: a_uuid,
                        id: 2,
                        name: "two".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        description: "two".to_string(),
                        file: "two.c".to_string(),
                        line: "2".to_string(),
                    },
                ),
                (
                    (a_uuid, 3),
                    EventMeta {
                        component_id: a_uuid,
                        id: 3,
                        name: "three".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        description: "three".to_string(),
                        file: "three.c".to_string(),
                        line: "3".to_string(),
                    },
                ),
                (
                    (a_uuid, 4),
                    EventMeta {
                        component_id: a_uuid,
                        id: 4,
                        name: "four".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        description: "four".to_string(),
                        file: "four.c".to_string(),
                        line: "4".to_string(),
                    },
                ),
            ]
            .into_iter()
            .collect(),
            probes_to_components: vec![(1, a_uuid), (2, a_uuid), (3, a_uuid), (4, a_uuid)]
                .into_iter()
                .collect(),
            component_names: vec![(a_uuid.to_string(), "component".to_string())]
                .into_iter()
                .collect(),
        }
    }

    const EXPECTED_GRAPH: &str = "\
|   |   |   *   four @ four (1:4:1:1)
|   |   |   |
|   +<--+   |   two merged a snapshot from three
|   |   |   |
|   |   |   *   four @ four (1:4:1:2)
|   |   |   |
|   *   |   |   two @ two (1:2:1:3)
|   |   |   |
|   |   |   *   four @ four (1:4:1:3)
|   |   |   |
+-->+   |   |   two merged a snapshot from one
|   |   |   |
*   |   |   |   one @ one (1:1:1:2)
|   |   |   |
|   *   |   |   two @ two (1:2:1:6)
|   |   |   |
*   |   |   |   one @ one (1:1:1:3)
|   |   |   |
|   +-->+   |   three merged a snapshot from two
|   |   |   |
+<--+   |   |   one merged a snapshot from two
|   |   |   |
|   *   |   |   two @ two (1:2:1:9)
|   |   |   |
|   *   |   |   two @ two (1:2:1:10)
|   |   |   |
";

    #[test]
    fn test_graph() {
        let now = Utc::now();
        let probe1 = ProbeId::new(1).unwrap();
        let event1 = EventId::new(1).unwrap();

        let probe2 = ProbeId::new(2).unwrap();
        let event2 = EventId::new(2).unwrap();

        let probe3 = ProbeId::new(3).unwrap();

        let probe4 = ProbeId::new(4).unwrap();
        let event4 = EventId::new(4).unwrap();

        let trace = vec![
            // Probe 1
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 0,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 1,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 2,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event1),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 3,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event1),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 4,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 5,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(3),
                }),
                receive_time: now,
            },
            // Probe 2
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 0,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 1,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 2,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 3,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event2),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 4,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 5,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 6,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event2),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 7,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(3),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 8,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(4),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 9,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event2),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 10,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event2),
                receive_time: now,
            },
            // Probe 3
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 0,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 1,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 2,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 4,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                }),
                receive_time: now,
            },
            // Probe 4
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 0,
                probe_id: probe4,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe4,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 1,
                probe_id: probe4,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event4),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 2,
                probe_id: probe4,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event4),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 3,
                probe_id: probe4,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                data: LogEntryData::Event(event4),
                receive_time: now,
            },
        ];

        let cfg = cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
        };
        let (probes, clock_rows) = sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }
}
