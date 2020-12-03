use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Write,
    io::Write as WriteIo,
};

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{LogEntryData, ReportLogEntry};

use crate::{
    description_format::DescriptionFormat,
    hopefully,
    log::{color, format, Cfg, Log},
    meta,
};

// 2 empty columns between each timeline.
const COL_SPACE: &str = "  ";
const COL_EDGE: &str = "--";

pub(super) fn print_as_graph<W: WriteIo>(
    mut probes: BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    clock_rows: Vec<ReportLogEntry>,
    cfg: &Cfg,
    l: &Log,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    // Our “watch dog”. This ticks while the outer loop is
    // productive. If it stops ticking, we're done.
    let mut count = 0;

    // The timelines that are currently blocked and waiting the other
    // end of an egde to show up.
    let mut blocked_tls: HashMap<ProbeId, HashSet<(ProbeId, LogicalClock)>> = HashMap::new();

    // How many timelines are there?
    let n_probes = probes.len();
    // Probes mapped to their indices.
    let indices = probes
        .keys()
        .enumerate()
        .map(|(idx, id)| (*id, idx))
        .collect::<HashMap<ProbeId, usize>>();

    loop {
        let init_count = count;
        for (idx, (probe_id, log)) in probes.iter_mut().enumerate() {
            if let Some(row) = log.pop() {
                match row.data {
                    LogEntryData::Event(id) | LogEntryData::EventWithTime(.., id) => {
                        let blocked = blocked_tls
                            .get(probe_id)
                            .map(|t| !t.is_empty())
                            .unwrap_or(false);
                        if !blocked {
                            let event_name = meta::get_event_meta(&cfg, &probe_id, &id)
                                .map(|em| em.name.clone())
                                .unwrap_or_else(|_| probe_id.get_raw().to_string());
                            let probe_name = cfg
                                .probes
                                .get(&probe_id.get_raw())
                                .map(|pm| pm.name.clone())
                                .unwrap_or_else(|| probe_id.get_raw().to_string());
                            if let Some(ref fmt) = l.format {
                                print_event_row(
                                    &format::format(cfg, &row, fmt),
                                    idx,
                                    n_probes,
                                    &mut stream,
                                )?;
                            } else {
                                print_event_row(
                                    &format!(
                                        "{} {} {}",
                                        color::white(&event_name),
                                        color::colorize_probe(idx, &format!("@ {}", probe_name)),
                                        color::colorize_coord(&row.coordinate())
                                    ),
                                    idx,
                                    n_probes,
                                    &mut stream,
                                )?;

                                handle_graph_verbosity(
                                    l,
                                    probe_id,
                                    &id,
                                    n_probes,
                                    None,
                                    cfg,
                                    &mut stream,
                                )?;
                            }

                            print_info_row(n_probes, "", "", "", &mut stream)?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::EventWithPayload(id, pl)
                    | LogEntryData::EventWithPayloadWithTime(.., id, pl) => {
                        let blocked = blocked_tls
                            .get(probe_id)
                            .map(|t| !t.is_empty())
                            .unwrap_or(false);
                        if !blocked {
                            let event_meta = meta::get_event_meta(&cfg, &probe_id, &id);
                            let event_name = event_meta
                                .as_ref()
                                .map(|em| em.name.clone())
                                .unwrap_or_else(|_| probe_id.get_raw().to_string());
                            let description = event_meta.map(|em| em.description.clone()).ok();
                            let probe_name = cfg
                                .probes
                                .get(&probe_id.get_raw())
                                .map(|pm| pm.name.clone())
                                .unwrap_or_else(|| probe_id.get_raw().to_string());
                            if let Some(ref fmt) = l.format {
                                print_event_row(
                                    &format::format(cfg, &row, fmt),
                                    idx,
                                    n_probes,
                                    &mut stream,
                                )?;
                            } else {
                                let event_msg = if let Some(msg) = description.and_then(|d| {
                                    if d.contains_formatting() {
                                        d.format_payload(&pl).ok()
                                    } else {
                                        None
                                    }
                                }) {
                                    format!(
                                        "{} {}: {}",
                                        color::colorize_probe(idx, &probe_name.to_string()),
                                        color::colorize_coord(&row.coordinate()),
                                        color::white(&msg),
                                    )
                                } else {
                                    format!(
                                        "{} {} {}",
                                        color::white(&event_name),
                                        color::colorize_probe(idx, &format!("@ {}", probe_name)),
                                        color::colorize_coord(&row.coordinate())
                                    )
                                };
                                print_event_row(&event_msg, idx, n_probes, &mut stream)?;

                                handle_graph_verbosity(
                                    l,
                                    probe_id,
                                    &id,
                                    n_probes,
                                    Some(pl),
                                    cfg,
                                    &mut stream,
                                )?;
                            }
                            print_info_row(n_probes, "", "", "", &mut stream)?;
                        } else {
                            log.push(row);
                        }
                    }
                    LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
                        // This is a local clock.
                        if lc.id == *probe_id {
                            // The self-clock `0` is useful from a
                            // causal standpoint, but from a
                            // coordinating-timelines standpoint, it's
                            // ambiguous because it appears whether a
                            // snapshot was produced or not.
                            if lc.pack().1 != 0 {
                                if let Some(next) = log.pop() {
                                    match next.data.trace_clock() {
                                        Some(next_lc) => {
                                            if next_lc.id == *probe_id {
                                                handle_source_edge(
                                                    cfg,
                                                    lc,
                                                    probe_id,
                                                    n_probes,
                                                    &clock_rows,
                                                    &mut blocked_tls,
                                                    idx,
                                                    &indices,
                                                    &mut stream,
                                                )?;
                                            }
                                        }
                                        None => {
                                            handle_source_edge(
                                                cfg,
                                                lc,
                                                probe_id,
                                                n_probes,
                                                &clock_rows,
                                                &mut blocked_tls,
                                                idx,
                                                &indices,
                                                &mut stream,
                                            )?;
                                        }
                                    }
                                    log.push(next);
                                } else {
                                    handle_source_edge(
                                        cfg,
                                        lc,
                                        probe_id,
                                        n_probes,
                                        &clock_rows,
                                        &mut blocked_tls,
                                        idx,
                                        &indices,
                                        &mut stream,
                                    )?;
                                }
                            }
                        // This is a foreign clock: `lc.id != probe_id`.
                        } else {
                            let from_name = cfg
                                .probes
                                .get(&lc.id.get_raw())
                                .map(|pm| pm.name.clone())
                                .unwrap_or_else(|| lc.id.get_raw().to_string());
                            let to_name = cfg
                                .probes
                                .get(&probe_id.get_raw())
                                .map(|pm| pm.name.clone())
                                .unwrap_or_else(|| probe_id.get_raw().to_string());
                            let from_idx = indices.get(&lc.id);
                            if let Some(mut neighbor) = blocked_tls.remove(&lc.id) {
                                if neighbor.remove(&(*probe_id, lc)) {
                                    print_edge_line(
                                        *indices.get(&lc.id).unwrap(),
                                        idx,
                                        &from_name,
                                        &to_name,
                                        n_probes,
                                        &mut stream,
                                    )?;
                                    print_info_row(n_probes, "", "", "", &mut stream)?;
                                    blocked_tls.insert(lc.id, neighbor);
                                } else {
                                    let is_present = clock_rows.iter().any(|r| {
                                        lc.id == r.probe_id
                                            && r.data.trace_clock() == Some(lc.next())
                                    });
                                    if is_present {
                                        let self_tl = blocked_tls
                                            .entry(*probe_id)
                                            .or_insert_with(HashSet::new);
                                        self_tl.insert((lc.id, lc));
                                    } else {
                                        print_missing_edge_line(
                                            from_idx,
                                            &from_name,
                                            idx,
                                            &to_name,
                                            n_probes,
                                            l.probe.is_some(),
                                            &mut stream,
                                        )?;
                                    }
                                    blocked_tls.insert(lc.id, neighbor);
                                }
                            } else {
                                let is_present = clock_rows.iter().any(|r| {
                                    lc.id == r.probe_id && r.data.trace_clock() == Some(lc.next())
                                });
                                if is_present {
                                    let self_tl =
                                        blocked_tls.entry(*probe_id).or_insert_with(HashSet::new);
                                    self_tl.insert((lc.id, lc));
                                } else {
                                    print_missing_edge_line(
                                        from_idx,
                                        &from_name,
                                        idx,
                                        &to_name,
                                        n_probes,
                                        l.probe.is_some(),
                                        &mut stream,
                                    )?;
                                    print_info_row(n_probes, "", "", "", &mut stream)?;
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
    probe_id: &ProbeId,
    eid: &EventId,
    n_probes: usize,
    pl: Option<u32>,
    cfg: &Cfg,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let event_meta = meta::get_event_meta(&cfg, &probe_id, &eid);
    let probe_meta = cfg.probes.get(&probe_id.get_raw());
    if l.verbose != 0 && event_meta.is_ok() {
        let emeta = event_meta.expect("just checked that event meta is_some");
        print_info_row(
            n_probes,
            "description",
            &emeta.description,
            "    ",
            &mut stream,
        )?;
        // TODO(dan@auxon.io): Interpolate log-style payload / string
        // combos here if they're present.
        // https://github.com/auxoncorp/modality-probe/issues/281
        if let Some(pp) = meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), pl)? {
            print_info_row(n_probes, "payload", &pp, "    ", &mut stream)?;
        }
        print_info_row(
            n_probes,
            "tags",
            &emeta.tags.replace(";", ", "),
            "    ",
            &mut stream,
        )?;
        if !emeta.file.is_empty() && !emeta.line.is_empty() {
            print_info_row(
                n_probes,
                "source",
                &format!("\"{}#L{}\"", emeta.file, emeta.line),
                "    ",
                &mut stream,
            )?;
        }
    }
    if l.verbose > 1 && probe_meta.is_some() {
        let pmeta = probe_meta.expect("just checked that probe meta is_some");
        print_info_row(
            n_probes,
            "probe tags",
            &pmeta.tags.replace(";", ", "),
            "    ",
            &mut stream,
        )?;
        print_info_row(
            n_probes,
            "probe source",
            &match (pmeta.file.is_empty(), pmeta.line.is_empty()) {
                (false, false) => format!("\"{}#L{}\"", pmeta.file, pmeta.line),
                (false, true) => format!("\"{}\"", pmeta.file),
                _ => "None".to_string(),
            },
            "    ",
            &mut stream,
        )?;
        let comp_name_or_id =
            if let Some(n) = cfg.component_names.get(&pmeta.component_id.to_string()) {
                n.to_string()
            } else {
                pmeta.component_id.to_string()
            };
        print_info_row(n_probes, "component", &comp_name_or_id, "    ", &mut stream)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn handle_source_edge<W: WriteIo>(
    cfg: &Cfg,
    lc: LogicalClock,
    probe_id: &ProbeId,
    n_probes: usize,
    clock_rows: &[ReportLogEntry],
    blocked_tls: &mut HashMap<ProbeId, HashSet<(ProbeId, LogicalClock)>>,
    idx: usize,
    indices: &HashMap<ProbeId, usize>,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    {
        let all_targs = clock_rows.iter().filter(|r| {
            let inner_lc = r.data.trace_clock().unwrap();
            r.probe_id != inner_lc.id && inner_lc == lc.prev()
        });
        let self_tl = blocked_tls.entry(*probe_id).or_insert_with(HashSet::new);
        for t in all_targs {
            self_tl.insert((t.probe_id, t.data.trace_clock().unwrap()));
        }
    }
    let mut self_tl = blocked_tls.remove(probe_id).unwrap();
    let mut to_rm = Vec::new();
    for (pid, c) in self_tl.iter() {
        if let Some(neighbor) = blocked_tls.get_mut(pid) {
            if neighbor.remove(&(*probe_id, *c)) {
                let from_name = cfg
                    .probes
                    .get(&probe_id.get_raw())
                    .map(|pm| pm.name.clone())
                    .unwrap_or_else(|| probe_id.get_raw().to_string());
                let to_name = cfg
                    .probes
                    .get(&pid.get_raw())
                    .map(|pm| pm.name.clone())
                    .unwrap_or_else(|| probe_id.get_raw().to_string());
                print_edge_line(
                    idx,
                    *indices.get(&pid).unwrap(),
                    &from_name,
                    &to_name,
                    n_probes,
                    &mut stream,
                )?;
                print_info_row(n_probes, "", "", "", &mut stream)?;
                to_rm.push((*pid, *c));
            }
        }
    }
    for c in to_rm {
        self_tl.remove(&c);
    }
    blocked_tls.insert(*probe_id, self_tl);
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
                write!(s, "{}{}", color::colorize_probe(i, "|"), COL_SPACE),
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
    key: &str,
    info: &str,
    indent: &str,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        // If the info string is empty and we're on the lat timeline,
        // don't include the column spacing.
        if i == n_probe.saturating_sub(1) && info.is_empty() {
            hopefully!(
                write!(s, "{}", color::colorize_probe(i, "|")),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "{}{}", color::colorize_probe(i, "|"), COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(
        write!(s, "{}{}", indent, color::colorize_info(key, info)),
        "Internal error formatting graph"
    )?;
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
                write!(
                    s,
                    "{}{}{}",
                    color::colorize_probe(from, "+"),
                    color::colorize_probe(from, &COL_EDGE[1..]),
                    color::colorize_probe(from, ">")
                ),
                "Internal error formatting graph"
            )?;
        // This timeline is the source (left-to-right).
        } else if l_to_r && i == from {
            hopefully!(
                write!(
                    s,
                    "{}{}",
                    color::colorize_probe(from, "+"),
                    color::colorize_probe(from, COL_EDGE)
                ),
                "Internal error formatting graph"
            )?;
        // This timeline is the source (right-to-left).
        } else if i == from {
            hopefully!(
                write!(s, "{}{}", color::colorize_probe(from, "+"), COL_SPACE),
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
                write!(
                    s,
                    "+{}{}",
                    color::colorize_probe(from, "<"),
                    color::colorize_probe(from, &COL_EDGE[1..])
                ),
                "Internal error formatting graph"
            )?;
        // In a left-to-right edge, write the head of the arrow.
        } else if l_to_r && i == to - 1 {
            hopefully!(
                write!(
                    s,
                    "{}{}",
                    color::colorize_probe(from, COL_EDGE),
                    color::colorize_probe(from, ">")
                ),
                "Internal error formatting graph"
            )?;
        // We're on a timeline that lay between the source and
        // target and the edge should “jump” it.
        } else if (l_to_r && i > from && i < to) || (i > to && i < from) {
            hopefully!(
                write!(
                    s,
                    "{}{}",
                    color::colorize_probe(from, "-"),
                    color::colorize_probe(from, COL_EDGE)
                ),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "{}{}", color::colorize_probe(i, "|"), COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(
        write!(
            s,
            "{}",
            color::colorize_merge(from_pname, from, to_pname, to),
        ),
        "Internal error formatting graph"
    )?;
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

fn print_missing_edge_line<W: WriteIo>(
    from_idx: Option<&usize>,
    from_name: &str,
    to_idx: usize,
    to_name: &str,
    n_probe: usize,
    single_probe_mode: bool,
    mut stream: W,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    for i in 0..n_probe {
        if i == to_idx && !single_probe_mode {
            hopefully!(
                write!(s, "?{}", COL_SPACE),
                "Internal error formatting graph"
            )?;
        } else if i == to_idx && single_probe_mode {
            hopefully!(
                write!(
                    s,
                    "+{}{}",
                    if let Some(fi) = from_idx {
                        color::colorize_probe(*fi, "<-").to_string()
                    } else {
                        "<-".to_string()
                    },
                    &COL_SPACE[2..]
                ),
                "Internal error formatting graph"
            )?;
        } else {
            hopefully!(
                write!(s, "{}{}", color::colorize_probe(i, "|"), COL_SPACE),
                "Internal error formatting graph"
            )?;
        }
    }
    hopefully!(
        if single_probe_mode {
            write!(
                s,
                "{}",
                if let Some(fi) = from_idx {
                    color::colorize_merge(from_name, *fi, to_name, to_idx)
                } else {
                    format!("{} merged a snapshot from {}", to_name, from_name)
                }
            )
        } else {
            write!(
                s,
                "{} expected a snapshot from {} but it is missing",
                color::colorize_probe(to_idx, to_name),
                if let Some(fi) = from_idx {
                    color::colorize_probe(*fi, from_name)
                } else {
                    from_name.to_string()
                },
            )
        },
        "Internal error formatting graph"
    )?;
    hopefully!(writeln!(stream, "{}", s), "Internal error formatting graph")?;
    Ok(())
}

#[cfg(test)]
pub(crate) mod test {
    use std::path::PathBuf;

    use chrono::Utc;

    use modality_probe::{EventId, NanosecondResolution, ProbeEpoch, ProbeTicks, WallClockId};
    use modality_probe_collector_common::{SequenceNumber, SessionId};

    use crate::{log, visualize::graph};

    use super::*;

    pub fn trace() -> Vec<ReportLogEntry> {
        let now = Utc::now();
        let probe1 = ProbeId::new(1).unwrap();
        let event1 = EventId::new(1).unwrap();

        let probe2 = ProbeId::new(2).unwrap();
        let event2 = EventId::new(2).unwrap();

        let probe3 = ProbeId::new(3).unwrap();

        let probe4 = ProbeId::new(4).unwrap();
        let event4 = EventId::new(4).unwrap();

        vec![
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(3),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(4),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(4),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(4),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(2),
                },
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
                clock: LogicalClock {
                    id: probe4,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe4,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe4,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe4,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
            },
        ]
    }

    const EXPECTED_GRAPH: &str = "\
|  |  |  *  four @ four (1:4:0:1:1)
|  |  |  |
|  +<-+  |  two merged a snapshot from three
|  |  |  |
|  |  |  *  four @ four (1:4:0:1:2)
|  |  |  |
|  *  |  |  two @ two (1:2:1:1:3)
|  |  |  |
|  |  |  *  four @ four (1:4:0:1:3)
|  |  |  |
+->+  |  |  two merged a snapshot from one
|  |  |  |
*  |  |  |  one @ one (1:1:1:1:2)
|  |  |  |
|  *  |  |  two @ two (1:2:2:1:6)
|  |  |  |
*  |  |  |  one @ one (1:1:1:1:3)
|  |  |  |
|  +->+  |  three merged a snapshot from two
|  |  |  |
+<-+  |  |  one merged a snapshot from two
|  |  |  |
|  *  |  |  two @ two (1:2:4:1:9)
|  |  |  |
|  *  |  |  two @ two (1:2:4:1:10)
|  |  |  |
";

    #[test]
    fn graph() {
        let trace = trace();
        let cfg = graph::test::cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
            format: None,
            radius: None,
            from: None,
            no_color: true,
        };
        {
            let mut b = color::COLORIZE.write().unwrap();
            *b = false;
        }
        let (probes, clock_rows) = log::sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }

    pub fn fanout_trace() -> Vec<ReportLogEntry> {
        let now = Utc::now();
        let probe1 = ProbeId::new(1).unwrap();
        let event1 = EventId::new(1).unwrap();

        let probe2 = ProbeId::new(2).unwrap();
        let event2 = EventId::new(2).unwrap();

        let probe3 = ProbeId::new(3).unwrap();
        let event3 = EventId::new(3).unwrap();

        vec![
            // Probe 1
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 0,
                probe_id: probe1,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
                data: LogEntryData::Event(event1),
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                sequence_index: 3,
                probe_id: probe2,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                clock: LogicalClock {
                    id: probe2,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                data: LogEntryData::Event(event3),
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                data: LogEntryData::Event(event3),
                receive_time: now,
            },
            ReportLogEntry {
                session_id: SessionId(1),
                sequence_number: SequenceNumber(1),
                sequence_index: 3,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                data: LogEntryData::Event(event3),
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
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
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
                sequence_index: 5,
                probe_id: probe3,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                clock: LogicalClock {
                    id: probe3,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(1),
                },
                data: LogEntryData::TraceClock(LogicalClock {
                    id: probe1,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                receive_time: now,
            },
        ]
    }

    const EXPECTED_FANOUT: &str = "\
|  |  *  three @ three (1:3:0:1:1)
|  |  |
+->+  |  two merged a snapshot from one
|  |  |
|  |  *  three @ three (1:3:0:1:2)
|  |  |
|  *  |  two @ two (1:2:1:1:3)
|  |  |
|  |  *  three @ three (1:3:0:1:3)
|  |  |
+---->+  three merged a snapshot from one
|  |  |
*  |  |  one @ one (1:1:1:1:2)
|  |  |
*  |  |  one @ one (1:1:1:1:3)
|  |  |
";

    #[test]
    fn fanout_graph() {
        let trace = fanout_trace();
        let cfg = graph::test::cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
            format: None,
            radius: None,
            from: None,
            no_color: true,
        };
        {
            let mut b = color::COLORIZE.write().unwrap();
            *b = false;
        }
        let (probes, clock_rows) = log::sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_FANOUT, std::str::from_utf8(&out).unwrap());
    }
}
