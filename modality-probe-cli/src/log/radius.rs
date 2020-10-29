use std::{
    collections::{BTreeMap, HashSet},
    convert::TryFrom,
};

use modality_probe::{LogicalClock, ProbeId};
use modality_probe_collector_common::{LogEntryData, ReportLogEntry, SequenceNumber};

use crate::{error::CmdError, give_up, hopefully, hopefully_ok};

use super::SortedProbes;

#[derive(PartialEq, Debug)]
pub struct Radius {
    distance: usize,
    probe_id: ProbeId,
    seq: SequenceNumber,
    seq_index: u32,
}

impl TryFrom<&str> for Radius {
    type Error = Box<CmdError>;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let sections: Vec<&str> = s.split(',').collect();
        if sections.len() != 2 {
            give_up!(format!(
                "{} is not a valid radius. It's missing either the coordinate or the distance",
                s
            ));
        }
        let coord = sections[0];
        let c_sections: Vec<&str> = coord.split(':').collect();
        if c_sections.len() != 4 {
            give_up!(format!("{} is not a valid coordinate", coord));
        }

        let distance = hopefully!(
            sections[1].parse::<usize>(),
            "Unable to parse the given distance"
        )?;

        let probe_id = {
            let raw_pid = hopefully!(
                c_sections[1].parse::<u32>(),
                "Unable to parse the given coordinate"
            )?;
            hopefully_ok!(
                ProbeId::new(raw_pid),
                "Unable to parse the given coordinate"
            )?
        };

        let seq = {
            let s = hopefully!(
                c_sections[2].parse::<u64>(),
                "Unable to parse the given coordinate"
            )?;
            SequenceNumber(s)
        };

        let seq_index = hopefully!(
            c_sections[3].parse::<u32>(),
            "Unable to parse the given coordinate"
        )?;

        Ok(Radius {
            distance,
            probe_id,
            seq,
            seq_index,
        })
    }
}

pub fn truncate_to_radius(probes: SortedProbes, radius: Radius) -> SortedProbes {
    let target_tl = match probes.0.get(&radius.probe_id) {
        Some(tl) => tl,
        None => return (BTreeMap::new(), vec![]),
    };
    let target_tl_len = target_tl.len();
    if target_tl_len == 0 {
        return (BTreeMap::new(), vec![]);
    }
    let coord_idx = match target_tl
        .iter()
        .position(|row| row.sequence_number == radius.seq && row.sequence_index == radius.seq_index)
    {
        Some(i) => i,
        None => return (BTreeMap::new(), vec![]),
    };

    let start = if coord_idx < radius.distance {
        0
    } else {
        coord_idx - radius.distance
    };
    let end = if coord_idx + radius.distance >= target_tl_len {
        target_tl_len - 1
    } else {
        coord_idx + radius.distance
    };

    let mut new_probes = BTreeMap::new();

    let trunc_tl = target_tl
        .iter()
        .enumerate()
        .skip_while(|(idx, _)| *idx < start)
        .take_while(|(idx, _)| *idx <= end)
        .map(|(_, row)| row)
        .collect::<Vec<&ReportLogEntry>>();

    let mut clock_rows = Vec::new();
    let mut included_rows = HashSet::new();
    drain_truncated_log(
        trunc_tl,
        &mut new_probes,
        &mut included_rows,
        &mut clock_rows,
        &probes,
        radius.distance as i64,
    );

    for row in clock_rows.iter() {
        let p = new_probes.entry(row.probe_id).or_insert_with(Vec::new);
        p.push(row.clone());
    }
    for plog in new_probes.values_mut() {
        plog.sort_by_key(|p| std::cmp::Reverse((p.sequence_number, p.sequence_index)));
    }

    (new_probes, clock_rows)
}

fn drain_truncated_log(
    mut log: Vec<&ReportLogEntry>,
    new_probes: &mut BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    included_rows: &mut HashSet<(ProbeId, SequenceNumber, u32)>,
    clock_rows: &mut Vec<ReportLogEntry>,
    probes: &SortedProbes,
    dist: i64,
) {
    let mut d = dist;
    let mut idx = 0;
    while let Some(row) = log.pop() {
        match row.data {
            LogEntryData::Event(..) | LogEntryData::EventWithTime(..) => {
                if included_rows.insert((row.probe_id, row.sequence_number, row.sequence_index)) {
                    let p = new_probes.entry(row.probe_id).or_insert_with(Vec::new);
                    p.push(row.clone());
                }
            }
            LogEntryData::EventWithPayload(..) | LogEntryData::EventWithPayloadWithTime(..) => {
                if included_rows.insert((row.probe_id, row.sequence_number, row.sequence_index)) {
                    let p = new_probes.entry(row.probe_id).or_insert_with(Vec::new);
                    p.push(row.clone());
                }
            }
            LogEntryData::TraceClock(lc) | LogEntryData::TraceClockWithTime(.., lc) => {
                if included_rows.insert((row.probe_id, row.sequence_number, row.sequence_index)) {
                    clock_rows.push(row.clone());
                    if lc.id != row.probe_id {
                        if let Some(sender) = probes
                            .1
                            .iter()
                            .find(|clock_row| {
                                clock_row.probe_id == lc.id
                                    && clock_row.data.trace_clock() == Some(lc)
                            })
                            .map(|row| row.probe_id)
                        {
                            handle_snap_merge(
                                lc,
                                d,
                                sender,
                                probes,
                                new_probes,
                                included_rows,
                                clock_rows,
                            );
                        }
                    } else if lc.pack().1 != 0 {
                        if let Some(next) = log.pop() {
                            if let Some(next_lc) = next.data.trace_clock() {
                                if next_lc.id == row.probe_id {
                                    let receivers = probes
                                        .1
                                        .iter()
                                        .filter(|clock_row| {
                                            clock_row.probe_id != row.probe_id
                                                && clock_row.data.trace_clock().unwrap()
                                                    == lc.prev()
                                        })
                                        .map(|clock_row| clock_row.probe_id);
                                    for receiver in receivers {
                                        handle_snap_produce(
                                            lc,
                                            d,
                                            receiver,
                                            probes,
                                            new_probes,
                                            included_rows,
                                            clock_rows,
                                        );
                                    }
                                }
                            }
                            let receivers = probes
                                .1
                                .iter()
                                .filter(|clock_row| {
                                    clock_row.probe_id != row.probe_id
                                        && clock_row.data.trace_clock().unwrap() == lc.prev()
                                })
                                .map(|clock_row| clock_row.probe_id);
                            for receiver in receivers {
                                handle_snap_produce(
                                    lc,
                                    d,
                                    receiver,
                                    probes,
                                    new_probes,
                                    included_rows,
                                    clock_rows,
                                );
                            }
                            log.push(next);
                        } else {
                            let receivers = probes
                                .1
                                .iter()
                                .filter(|clock_row| {
                                    clock_row.probe_id != row.probe_id
                                        && clock_row.data.trace_clock().unwrap() == lc.prev()
                                })
                                .map(|clock_row| clock_row.probe_id);
                            for receiver in receivers {
                                handle_snap_produce(
                                    lc,
                                    d,
                                    receiver,
                                    probes,
                                    new_probes,
                                    included_rows,
                                    clock_rows,
                                );
                            }
                        }
                    }
                }
            }
            _ => (),
        }
        d = dist - (dist - idx).abs();
        idx += 1;
    }
}

fn handle_snap_produce(
    clock: LogicalClock,
    dist: i64,
    receiver: ProbeId,
    probes: &SortedProbes,
    new_probes: &mut BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    included_rows: &mut HashSet<(ProbeId, SequenceNumber, u32)>,
    clock_rows: &mut Vec<ReportLogEntry>,
) {
    if let Some(neighbor) = probes.0.get(&receiver) {
        if let Some(start) = neighbor
            .iter()
            .position(|row| row.data.trace_clock() == Some(clock.prev()))
        {
            let neighbor_len = neighbor.len();
            let end = if start + dist as usize >= neighbor_len {
                neighbor_len - 1
            } else {
                start + dist as usize
            };
            let trunc_neighbor = neighbor
                .iter()
                .enumerate()
                .skip_while(|(idx, _)| *idx < start)
                .take_while(|(idx, _)| *idx < end)
                .map(|(_, row)| row)
                .collect::<Vec<&ReportLogEntry>>();
            drain_truncated_log(
                trunc_neighbor,
                new_probes,
                included_rows,
                clock_rows,
                probes,
                dist,
            );
        }
    }
}

fn handle_snap_merge(
    clock: LogicalClock,
    dist: i64,
    receiver: ProbeId,
    probes: &SortedProbes,
    new_probes: &mut BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    included_rows: &mut HashSet<(ProbeId, SequenceNumber, u32)>,
    clock_rows: &mut Vec<ReportLogEntry>,
) {
    if let Some(neighbor) = probes.0.get(&receiver) {
        if let Some(end) = neighbor
            .iter()
            .position(|row| row.data.trace_clock() == Some(clock.next()))
        {
            let start = if end < dist as usize {
                0
            } else {
                end - dist as usize
            };

            let trunc_neighbor = neighbor
                .iter()
                .enumerate()
                .skip_while(|(idx, _)| *idx < start)
                .take_while(|(idx, _)| *idx <= end)
                .map(|(_, row)| row)
                .collect::<Vec<&ReportLogEntry>>();
            drain_truncated_log(
                trunc_neighbor,
                new_probes,
                included_rows,
                clock_rows,
                probes,
                dist,
            );
        }
    }
}

#[cfg(test)]
mod test {
    use std::{convert::TryFrom, path::PathBuf};

    use proptest::prelude::*;

    use crate::{log, log::Log, visualize::graph};

    use super::*;

    const EXPECTED_GRAPH: &str = "\
*   |   one @ one (1:1:1:2)
|   |
*   |   one @ one (1:1:1:3)
|   |
+<--+   one merged a snapshot from two
|   |
|   *   two @ two (1:2:1:9)
|   |
|   *   two @ two (1:2:1:10)
|   |
";

    proptest! {
        #[test]
        fn radius_rt(
            dist in proptest::num::usize::ANY,
            pid in proptest::num::u32::ANY,
            seq in proptest::num::u64::ANY,
            seq_index in proptest::num::u32::ANY,
        ) {
            let raid = format!("0:{}:{}:{},{}", pid, seq, seq_index, dist);
            if let Some(probe_id) = ProbeId::new(pid) {
                let init = Radius {
                    distance: dist,
                    seq: SequenceNumber(seq),
                    probe_id,
                    seq_index,
                };
                prop_assert_eq!(init, Radius::try_from(raid.as_ref()).unwrap());
            } else if let Err(err) = Radius::try_from(raid.as_ref()) {
                prop_assert_eq!(
                    "Unable to parse the given coordinate".to_string(),
                    err.msg
                );
            } else {
                panic!("failed");
            }
        }
    }

    #[test]
    fn radius_graph() {
        let trace = log::test::trace();
        let cfg = graph::test::cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
            format: None,
            radius: Some("1:1:1:2,3".to_string()),
        };
        let (probes, clock_rows) = log::sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        log::print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }
}
