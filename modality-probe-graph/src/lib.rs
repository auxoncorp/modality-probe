//! `modality-probe-graph` is a library that builds different types of node
//! and edge lists from a columnar, unordered collection of log
//! reports like the one that modality-probe-udp-collector creates.
use std::{collections::HashMap, hash::Hash};

use err_derive::Error;

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{EventLogEntry, Report, SequenceNumber};

/// A trait for the inner graph type of `EventDiagraph`. This enables
/// a custom inner graph that can be purpose built for a use-case, but
/// allows said graph to still be built by `EventDigraph`.
pub trait Graph {
    /// Add a node / vertex to the inner graph.
    fn add_node(&mut self, node: GraphEvent);
    /// Add an edge to the inner graph.
    fn add_edge(&mut self, source: GraphEvent, target: GraphEvent);
}

/// A node in the event digraph.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub struct GraphEvent {
    pub id: EventId,
    pub clock: LogicalClock,
    pub payload: Option<u32>,
    pub probe_id: ProbeId,
    pub seq: SequenceNumber,
    pub seq_idx: usize,
}

/// Errors returned by the `EventDigraph` methods.
#[derive(Debug, Error)]
pub enum Error {
    /// Encountered an error when using the writer when exporting a
    /// graph in a textual format.
    #[error(display = "Formatting graph failed: {}", _0)]
    Io(String),
    /// The graph builders iterate over a `Result` to leave room for
    /// deserialization; if a builder encounters a `Err`, this error
    /// is returned with that error's `display` implementation inside.
    #[error(display = "An item in the log iterator was an error variant: {}", _0)]
    ItemError(String),
    /// Encountered an unexpected inconsistency in the graph data.
    #[error(display = "Encountered an inconsistency in the graph data: {}", _0)]
    InconsistentData(&'static str),
}

/// A type that eats Modality Probe reports and stuffs them into its
/// inner graph type.
#[derive(Debug, PartialEq, Eq)]
pub struct EventDigraph<G: Graph> {
    /// The EventDigraph retains ownership of the inner graph, but
    /// must make it available so that its purpose-built functionality
    /// is accessible.
    pub graph: G,

    /// When a foreign trace clock is the last thing in a report
    /// chunk, we need to look up and hold on to the last event before
    /// that clock in the source probe, keyed by the probe id and the
    /// sequence number it appeared in the neighbor's log. That way,
    /// when we get the next chunk from that probe (the neighbor), we
    /// can draw the edge from this source to the first event in the
    /// next chunk.
    tail_pending_edge_sources: HashMap<(ProbeId, SequenceNumber), GraphEvent>,

    /// This is to carry a clock-span across chunks.
    last_event_by_probe_and_seq_num: HashMap<(ProbeId, SequenceNumber), GraphEvent>,

    /// This is the table used to look up the source events when a
    /// foreign clock is encountered in the log.
    last_event_by_probe_and_clock: HashMap<(ProbeId, u32), GraphEvent>,
}

impl<G: Graph> EventDigraph<G> {
    /// Construct an empty graph.
    pub fn new(graph: G) -> Self {
        EventDigraph {
            graph,
            tail_pending_edge_sources: HashMap::new(),
            last_event_by_probe_and_seq_num: HashMap::new(),
            last_event_by_probe_and_clock: HashMap::new(),
        }
    }

    /// Turn a report into nodes and edges on the graph.
    pub fn add_report(&mut self, report: &Report, include_internals: bool) -> Result<(), Error> {
        let probe_id = report.probe_id;
        let seq_num = report.seq_num;
        let mut prev_event = None;
        let mut prev_tc = None;
        let mut first_event = true;
        let mut self_clock = if let Some(sc) = report.frontier_clocks.get(0) {
            sc
        } else {
            return Err(Error::InconsistentData("missing self frontier clock"));
        };
        let mut pending_edges = vec![];
        // To properly abide sequence indices from the original
        // flattened log, we need to offset them by the number of
        // frontier clocks.
        let num_frontier_clocks = report.frontier_clocks.len();

        for (idx, ev) in report.event_log.iter().enumerate() {
            match ev {
                EventLogEntry::Event(id) | EventLogEntry::EventWithTime(.., id) => {
                    if include_internals || !id.is_internal() {
                        let node = GraphEvent {
                            probe_id,
                            id: *id,
                            clock: *self_clock,
                            payload: None,
                            seq: seq_num,
                            seq_idx: idx.saturating_add(num_frontier_clocks),
                        };
                        self.add_event_to_graph(
                            node,
                            &mut pending_edges,
                            &mut prev_event,
                            &mut prev_tc,
                            &mut first_event,
                            probe_id,
                            seq_num,
                        );
                    }
                }
                EventLogEntry::EventWithPayload(id, payload)
                | EventLogEntry::EventWithPayloadWithTime(.., id, payload) => {
                    if include_internals || !id.is_internal() {
                        let node = GraphEvent {
                            probe_id,
                            id: *id,
                            clock: *self_clock,
                            payload: Some(*payload),
                            seq: seq_num,
                            seq_idx: idx,
                        };
                        self.add_event_to_graph(
                            node,
                            &mut pending_edges,
                            &mut prev_event,
                            &mut prev_tc,
                            &mut first_event,
                            probe_id,
                            seq_num,
                        );
                    }
                }
                EventLogEntry::TraceClock(lc) | EventLogEntry::TraceClockWithTime(.., lc) => {
                    if lc.id == probe_id {
                        // when we see a clock, the previous event we
                        // saw is the last event from the previous
                        // clock span.
                        let prev_self_clock =
                            modality_probe::pack_clock_word(lc.epoch, lc.ticks).saturating_sub(1);
                        if let Some(prev) = prev_event {
                            self.last_event_by_probe_and_clock
                                .insert((probe_id, prev_self_clock), prev);
                        } else if idx == 0 {
                            // Or, if the first entry in the report is
                            // a self trace clock, we can lookup the
                            // last event from the previous report
                            // chunk and, if we have it, save it for
                            // future lookups.
                            if let Some(ple) = self
                                .last_event_by_probe_and_seq_num
                                .get(&(probe_id, seq_num.prev()))
                            {
                                self.last_event_by_probe_and_clock
                                    .insert((probe_id, prev_self_clock), *ple);
                            }
                        }
                        self_clock = lc;
                    } else {
                        pending_edges
                            .push((lc.id, modality_probe::pack_clock_word(lc.epoch, lc.ticks)));
                    }
                    prev_tc = Some(*lc);
                }
                EventLogEntry::WallClockTime(_t) => (),
            }
        }
        if let Some(pe) = prev_event {
            self.last_event_by_probe_and_seq_num
                .insert((probe_id, seq_num), pe);
        }
        if let Some(ptc) = prev_tc {
            if ptc.id != probe_id {
                if let Some(ev) = self.last_event_by_probe_and_clock.get(&(
                    ptc.id,
                    modality_probe::pack_clock_word(ptc.epoch, ptc.ticks),
                )) {
                    self.tail_pending_edge_sources
                        .insert((probe_id, seq_num), *ev);
                }
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn add_event_to_graph(
        &mut self,
        node: GraphEvent,
        pending_edges: &mut Vec<(ProbeId, u32)>,
        prev_event: &mut Option<GraphEvent>,
        prev_tc: &mut Option<LogicalClock>,
        first_event: &mut bool,
        probe_id: ProbeId,
        seq_num: SequenceNumber,
    ) {
        self.graph.add_node(node);
        if *first_event {
            if let Some(tail) = self.tail_pending_edge_sources.remove(&(probe_id, seq_num)) {
                self.graph.add_edge(tail, node);
            }
            if let Some(tail) = self
                .last_event_by_probe_and_seq_num
                .remove(&(probe_id, seq_num.prev()))
            {
                self.graph.add_edge(tail, node);
            }
            *first_event = false;
        }
        if let Some(prev) = prev_event {
            self.graph.add_edge(*prev, node);
        }
        for lc in pending_edges.iter() {
            if let Some(e) = self.last_event_by_probe_and_clock.get(lc) {
                self.graph.add_edge(*e, node);
            }
        }
        pending_edges.clear();
        *prev_event = Some(node);
        *prev_tc = None;
    }
}

#[cfg(any(test, feature = "test_support"))]
pub mod test_support {
    use chrono::prelude::*;

    use modality_probe_collector_common::LogFileRow;

    //   1
    //  / \   |
    // 2   3  |
    //  \ /   V
    //   4
    pub fn diamond() -> Vec<LogFileRow> {
        let now = Utc::now();
        vec![
            // 1
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
}

#[cfg(test)]
mod test {
    use std::{collections::HashSet, convert::TryInto};

    use chrono::prelude::*;

    use modality_probe::{EventId, ProbeEpoch, ProbeId, ProbeTicks};
    use modality_probe_collector_common::{LogFileRow, ReportIter};

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

    #[test]
    fn sanity() {
        let report_iter = ReportIter::new(
            test_support::diamond()
                .into_iter()
                .map(|e| (&e).try_into().unwrap())
                .peekable(),
        );

        let inner = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };
        let mut expected = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };

        let mut graph = EventDigraph::new(inner);
        for report in report_iter {
            graph.add_report(&report, false).unwrap();
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
            seq_idx: 1,
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
            seq_idx: 3,
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
            seq_idx: 3,
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
            seq_idx: 5,
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

    #[test]
    fn internals() {
        let now = Utc::now();
        let log = vec![
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 0,
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
                probe_id: 1,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(EventId::EVENT_PRODUCED_EXTERNAL_REPORT.get_raw()),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 3,
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
                probe_id: 1,
                fc_probe_id: None,
                fc_probe_epoch: None,
                fc_probe_clock: None,
                event_id: Some(EventId::EVENT_PRODUCED_EXTERNAL_REPORT.get_raw()),
                event_payload: None,
                tc_probe_id: None,
                tc_probe_epoch: None,
                tc_probe_clock: None,
            },
            LogFileRow {
                session_id: 1,
                sequence_number: 1,
                sequence_index: 4,
                time_resolution: 0,
                wall_clock_id: 0,
                receive_time: now,
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
        ];
        let report_iter =
            ReportIter::new(log.into_iter().map(|e| (&e).try_into().unwrap()).peekable());

        let inner = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };
        let mut expected = NodeAndEdgeList {
            nodes: HashSet::new(),
            edges: HashSet::new(),
        };

        let mut graph = EventDigraph::new(inner);
        for report in report_iter {
            graph.add_report(&report, false).unwrap();
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
            seq_idx: 1,
        };
        let one_prime = GraphEvent {
            id: EventId::new(1).unwrap(),
            payload: None,
            probe_id: ProbeId::new(1).unwrap(),
            clock: LogicalClock {
                id: ProbeId::new(1).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
            seq: SequenceNumber(1),
            seq_idx: 4,
        };
        expected.add_node(one);
        expected.add_node(one_prime);

        expected.add_edge(one, one_prime);

        assert_eq!(graph.graph, expected);
    }
}
