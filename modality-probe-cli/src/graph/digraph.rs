//! A simple directed graph type that compliles node and edge lists.
use std::{collections::HashMap, hash::Hash};

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{EventLogEntry, Report, SequenceNumber};

use crate::graph::Error;

pub trait Graph {
    fn add_node(&mut self, node: GraphEvent);
    fn add_edge(&mut self, source: GraphEvent, target: GraphEvent);
}

#[derive(Debug, PartialEq, Eq)]
pub struct Digraph<G: Graph> {
    graph: G,

    // When a foreign trace clock is the last thing in a report chunk,
    // we need to look up and hold on to the last event before that
    // clock in the source probe, keyed by the probe id and the
    // sequence number it appeared in the neighbor's log. That way,
    // when we get the next chunk from that probe (the neighbor), we
    // can draw the edge from this source to the first event in the
    // next chunk.
    tail_pending_edge_sources: HashMap<(ProbeId, SequenceNumber), GraphEvent>,

    // This is to carry a clock-span across chunks.
    last_event_by_probe_and_seq_num: HashMap<(ProbeId, SequenceNumber), GraphEvent>,

    // This is the table used to look up the source events when a
    // foreign clock is encountered in the log.
    last_event_by_probe_and_clock: HashMap<(ProbeId, u32), GraphEvent>,
}

impl<G: Graph> Digraph<G> {
    /// Construct an empty graph.
    pub fn new(graph: G) -> Self {
        Digraph {
            graph,
            tail_pending_edge_sources: HashMap::new(),
            last_event_by_probe_and_seq_num: HashMap::new(),
            last_event_by_probe_and_clock: HashMap::new(),
        }
    }

    pub fn add_report(&mut self, report: &Report) -> Result<(), Error> {
        let probe_id = report.probe_id;
        let seq_num = report.seq_num;
        let mut prev_event = None;
        let mut first_event = true;
        let mut self_clock = if let Some(sc) = report.frontier_clocks.get(0) {
            sc
        } else {
            return Err(Error::InconsistentData("missing self frontier clock"));
        };
        let mut pending_edges = vec![];

        for (idx, ev) in report.event_log.iter().enumerate() {
            match ev {
                EventLogEntry::Event(id) => {
                    let node = GraphEvent {
                        probe_id,
                        id: *id,
                        clock: *self_clock,
                        payload: None,
                        seq: seq_num,
                        seq_idx: idx,
                    };
                    self.graph.add_node(node);
                    if first_event {
                        if let Some(tail) =
                            self.tail_pending_edge_sources.remove(&(probe_id, seq_num))
                        {
                            self.graph.add_edge(tail, node);
                        }
                        if let Some(tail) = self
                            .last_event_by_probe_and_seq_num
                            .remove(&(probe_id, seq_num))
                        {
                            self.graph.add_edge(tail, node);
                        }
                        first_event = false;
                    }
                    if let Some(prev) = prev_event {
                        self.graph.add_edge(prev, node);
                    }
                    for lc in pending_edges.iter() {
                        if let Some(e) = self.last_event_by_probe_and_clock.get(lc) {
                            self.graph.add_edge(*e, node);
                        }
                    }
                    pending_edges.clear();
                    prev_event = Some(node);
                }
                EventLogEntry::EventWithPayload(id, payload) => {
                    let node = GraphEvent {
                        probe_id,
                        id: *id,
                        clock: *self_clock,
                        payload: Some(*payload),
                        seq: seq_num,
                        seq_idx: idx,
                    };
                    self.graph.add_node(node);
                    if first_event {
                        if let Some(tail) =
                            self.tail_pending_edge_sources.remove(&(probe_id, seq_num))
                        {
                            self.graph.add_edge(tail, node);
                        }
                        if let Some(tail) = self
                            .last_event_by_probe_and_seq_num
                            .remove(&(probe_id, seq_num))
                        {
                            self.graph.add_edge(tail, node);
                        }
                        first_event = false;
                    }
                    if let Some(prev) = prev_event {
                        self.graph.add_edge(prev, node);
                    }
                    for lc in pending_edges.iter() {
                        if let Some(e) = self.last_event_by_probe_and_clock.get(lc) {
                            self.graph.add_edge(*e, node);
                        }
                    }
                    pending_edges.clear();
                    prev_event = Some(node);
                }
                EventLogEntry::TraceClock(lc) => {
                    if lc.id == probe_id {
                        // when we see a clock, the previous event we
                        // saw is the last event from the previous
                        // clock span.
                        if let Some(prev) = prev_event {
                            self.last_event_by_probe_and_clock.insert(
                                (
                                    probe_id,
                                    modality_probe::pack_clock_word(lc.epoch, lc.ticks)
                                        .saturating_sub(1),
                                ),
                                prev,
                            );
                        }
                        self_clock = lc;
                    } else {
                        pending_edges
                            .push((lc.id, modality_probe::pack_clock_word(lc.epoch, lc.ticks)));
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub struct GraphEvent {
    id: EventId,
    clock: LogicalClock,
    payload: Option<u32>,
    probe_id: ProbeId,
    seq: SequenceNumber,
    seq_idx: usize,
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use chrono::prelude::*;

    use modality_probe::{EventId, ProbeEpoch, ProbeId, ProbeTicks};
    use modality_probe_collector_common::{csv::CsvReportIter, LogFileRow};

    use super::*;

    #[derive(PartialEq, Debug)]
    struct NodeAndEdgeList {
        nodes: HashSet<GraphEvent>,
        edges: HashSet<(GraphEvent, GraphEvent)>,
    }

    impl Graph for NodeAndEdgeList {
        fn add_node(&mut self, node: GraphEvent) {
            self.nodes.insert(node);
        }

        fn add_edge(&mut self, source: GraphEvent, target: GraphEvent) {
            self.edges.insert((source, target));
        }
    }

    //   1
    //  / \   |
    // 2   3  |
    //  \ /   V
    //   4
    fn diamond() -> Vec<LogFileRow> {
        let now = Utc::now();
        vec![
            // 1
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                receive_time: now.clone(),
                probe_id: 1,
                fc_probe_id: Some(1),
                fc_probe_epoch: Some(0),
                fc_probe_clock: Some(0),
                event_id: None,
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 1,
                receive_time: now.clone(),
                probe_id: 1,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(1),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 2,
                receive_time: now.clone(),
                probe_id: 1,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(1),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            // 2
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                receive_time: now.clone(),
                probe_id: 2,
                fc_probe_id: Some(2),
                fc_probe_epoch: Some(0),
                fc_probe_clock: Some(0),
                event_id: None,
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 1,
                receive_time: now.clone(),
                probe_id: 2,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(2),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 2,
                receive_time: now.clone(),
                probe_id: 2,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(1),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(0),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 3,
                receive_time: now.clone(),
                probe_id: 2,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(2),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 4,
                receive_time: now.clone(),
                probe_id: 2,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(2),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(2),
            },
            // 3
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                receive_time: now.clone(),
                probe_id: 3,
                fc_probe_id: Some(3),
                fc_probe_epoch: Some(0),
                fc_probe_clock: Some(0),
                event_id: None,
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 1,
                receive_time: now.clone(),
                probe_id: 3,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(3),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 2,
                receive_time: now.clone(),
                probe_id: 3,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(1),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(0),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 3,
                receive_time: now.clone(),
                probe_id: 3,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(3),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 4,
                receive_time: now.clone(),
                probe_id: 3,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(3),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(2),
            },
            // 4
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: Some(4),
                fc_probe_epoch: Some(0),
                fc_probe_clock: Some(0),
                event_id: None,
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 1,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(4),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 2,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(2),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 1,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(4),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(2),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 3,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: None,
                event_payload: None,
                tc_probe_id: Some(3),
                tc_probe_epoch: Some(0),
                tc_probe_clock: Some(1),
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 5,
                receive_time: now.clone(),
                probe_id: 4,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(4),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
        ]
    }

    #[test]
    fn complete() {
        let report_iter = CsvReportIter {
            report_items: diamond().into_iter().map(Ok).peekable(),
            error: None,
        };

        let inner = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };
        let mut expected = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };

        let mut graph = Digraph::new(inner);
        for report in report_iter {
            graph.add_report(&report.unwrap()).unwrap();
        }

        let one = GraphEvent {
            id: EventId::new(1).unwrap(),
            payload: None,
            probe_id: ProbeId::new(1).unwrap(),
            clock: LogicalClock {
                id: ProbeId::new(1).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
            seq: SequenceNumber(1),
            seq_idx: 0,
        };
        let two = GraphEvent {
            id: EventId::new(2).unwrap(),
            payload: None,
            probe_id: ProbeId::new(2).unwrap(),
            clock: LogicalClock {
                id: ProbeId::new(2).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(1),
            },
            seq: SequenceNumber(1),
            seq_idx: 2,
        };
        let three = GraphEvent {
            id: EventId::new(3).unwrap(),
            payload: None,
            probe_id: ProbeId::new(3).unwrap(),
            clock: LogicalClock {
                id: ProbeId::new(3).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(1),
            },
            seq: SequenceNumber(1),
            seq_idx: 2,
        };
        let four = GraphEvent {
            id: EventId::new(4).unwrap(),
            payload: None,
            probe_id: ProbeId::new(4).unwrap(),
            clock: LogicalClock {
                id: ProbeId::new(4).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(2),
            },
            seq: SequenceNumber(1),
            seq_idx: 4,
        };
        expected.add_node(one);
        expected.add_node(two);
        expected.add_node(three);
        expected.add_node(four);

        expected.add_edge(one, two);
        expected.add_edge(one, three);
        expected.add_edge(two, four);
        expected.add_edge(three, four);

        assert_eq!(
            graph.graph, expected,
            "\n{:#?}\n{:#?}",
            graph.graph, expected
        );
    }
}
