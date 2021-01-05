use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashSet},
    convert::TryFrom,
};

use modality_probe::{LogicalClock, ProbeId};
use modality_probe_collector_common::{LogEntryData, ReportLogEntry, SequenceNumber};

use crate::{error::CmdError, give_up, hopefully, hopefully_ok};

use super::SortedProbes;

#[derive(PartialEq, Debug)]
pub struct Radius {
    pub distance: usize,
    pub probe_id: ProbeId,
    pub seq: SequenceNumber,
    pub seq_index: u32,
}

impl TryFrom<(&usize, &str)> for Radius {
    type Error = Box<CmdError>;
    fn try_from(r: (&usize, &str)) -> Result<Self, Self::Error> {
        let (distance, coord) = r;

        let c_sections: Vec<&str> = coord.split(':').collect();
        match c_sections.len().cmp(&4) {
            Ordering::Less => {
                give_up!(format!(
                    "Invalid coordinate: {} is missing a section",
                    coord
                ));
            }
            Ordering::Greater => {
                give_up!(format!(
                    "Invalid coordinate: {} has too many sections",
                    coord
                ));
            }
            _ => (),
        }

        let probe_id = {
            let raw_pid = hopefully!(
                c_sections[1].parse::<u32>(),
                format!(
                    "Unable to parse the given coordinate: {}:->{}<-:{}:{}",
                    c_sections[0], c_sections[1], c_sections[2], c_sections[3]
                )
            )?;
            hopefully_ok!(
                ProbeId::new(raw_pid),
                format!(
                    "Unable to parse the given coordinate: {}:->{}<-:{}:{}",
                    c_sections[0], c_sections[1], c_sections[2], c_sections[3]
                )
            )?
        };

        let seq = {
            let s = hopefully!(
                c_sections[2].parse::<u64>(),
                format!(
                    "Unable to parse the given coordinate: {}:{}:->{}<-:{}",
                    c_sections[0], c_sections[1], c_sections[2], c_sections[3]
                )
            )?;
            SequenceNumber(s)
        };

        let seq_index = hopefully!(
            c_sections[3].parse::<u32>(),
            format!(
                "Unable to parse the given coordinate: {}:{}:{}:->{}<-",
                c_sections[0], c_sections[1], c_sections[2], c_sections[3]
            )
        )?;

        Ok(Radius {
            distance: *distance,
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

    (
        new_probes,
        clock_rows
            .into_iter()
            .map(|row| (row.probe_id, row.data.trace_clock().unwrap()))
            .collect(),
    )
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
                            .find(|(originator, clock)| originator == &lc.id && clock == &lc)
                            .map(|(originator, _)| originator)
                        {
                            handle_snap_merge(
                                lc,
                                d,
                                *sender,
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
                                        .filter(|(originator, clock)| {
                                            originator != &row.probe_id && clock == &lc.prev()
                                        })
                                        .map(|(originator, _)| originator);
                                    for receiver in receivers {
                                        handle_snap_produce(
                                            lc,
                                            d,
                                            *receiver,
                                            probes,
                                            new_probes,
                                            included_rows,
                                            clock_rows,
                                        );
                                    }
                                }
                            } else {
                                let receivers = probes
                                    .1
                                    .iter()
                                    .filter(|(originator, clock)| {
                                        originator != &row.probe_id && clock == &lc.prev()
                                    })
                                    .map(|(originator, _)| originator);
                                for receiver in receivers {
                                    handle_snap_produce(
                                        lc,
                                        d,
                                        *receiver,
                                        probes,
                                        new_probes,
                                        included_rows,
                                        clock_rows,
                                    );
                                }
                            }
                            log.push(next);
                        } else {
                            let receivers = probes
                                .1
                                .iter()
                                .filter(|(originator, clock)| {
                                    originator != &row.probe_id && clock == &lc.prev()
                                })
                                .map(|(originator, _)| originator);
                            for receiver in receivers {
                                handle_snap_produce(
                                    lc,
                                    d,
                                    *receiver,
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
    sender: ProbeId,
    probes: &SortedProbes,
    new_probes: &mut BTreeMap<ProbeId, Vec<ReportLogEntry>>,
    included_rows: &mut HashSet<(ProbeId, SequenceNumber, u32)>,
    clock_rows: &mut Vec<ReportLogEntry>,
) {
    if let Some(neighbor) = probes.0.get(&sender) {
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

    use crate::{
        log,
        log::{color, Log},
        visualize::graph,
    };

    use super::*;

    const EXPECTED_GRAPH: &str = "\
*  |  one @ one (1:1:1:1:2)
|  |
*  |  one @ one (1:1:1:1:3)
|  |
+<-+  one merged a snapshot from two
|  |
|  *  two @ two (1:2:4:1:9)
|  |
|  *  two @ two (1:2:4:1:10)
|  |
";

    proptest! {
        #[test]
        fn radius_rt(
            dist in proptest::num::usize::ANY,
            pid in proptest::num::u32::ANY,
            seq in proptest::num::u64::ANY,
            seq_index in proptest::num::u32::ANY,
        ) {
            let coord = format!("0:{}:{}:{}", pid, seq, seq_index);
            let raid = (&dist, coord.as_ref());
            if let Some(probe_id) = ProbeId::new(pid) {
                let init = Radius {
                    distance: dist,
                    seq: SequenceNumber(seq),
                    probe_id,
                    seq_index,
                };
                prop_assert_eq!(init, Radius::try_from(raid).unwrap());
            } else if let Err(err) = Radius::try_from(raid) {
                prop_assert!(
                    err.msg.contains("Unable to parse the given coordinate")
                );
            } else {
                panic!("failed");
            }
        }
    }

    #[test]
    fn radius_graph() {
        let trace = log::graph::test::trace();
        let cfg = graph::test::cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
            format: None,
            radius: Some(3),
            from: Some("1:1:1:2".to_string()),
            no_color: true,
        };
        {
            let mut b = color::COLORIZE.write().unwrap();
            *b = false;
        }
        let (probes, clock_rows) = log::sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        log::graph::print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }
}
