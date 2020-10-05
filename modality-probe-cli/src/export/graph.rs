use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    iter::Peekable,
};

use tinytemplate::TinyTemplate;

use modality_probe::ProbeId;
use modality_probe_collector_common::{ReportIter, ReportLogEntry};
use modality_probe_graph::{EventDigraph, Graph, GraphEvent};

use crate::{
    hopefully,
    meta::{self, Cfg},
};

use super::templates::{self, *};

pub fn log_to_graph<I>(
    log: Peekable<I>,
) -> Result<EventDigraph<NodeAndEdgeLists<GraphEvent>>, Box<dyn std::error::Error>>
where
    I: Iterator<Item = ReportLogEntry>,
{
    let mut graph = EventDigraph::new(NodeAndEdgeLists {
        nodes: HashSet::new(),
        edges: HashSet::new(),
    });
    let report_iter = ReportIter::new(log);
    for report in report_iter {
        hopefully!(
            graph.add_report(&report),
            "encountered an error reconstructing the graph"
        )?;
    }
    Ok(graph)
}

#[derive(Default)]
pub struct NodeAndEdgeLists<G>
where
    G: Hash + Eq,
{
    nodes: HashSet<G>,
    edges: HashSet<(G, G)>,
}

impl NodeAndEdgeLists<GraphEvent> {
    pub fn as_complete<'a>(&'a self, include_internals: bool) -> NodeAndEdgeLists<&'a GraphEvent> {
        let nodes = self
            .nodes
            .iter()
            .filter(|n| include_internals || !n.id.is_internal())
            .collect();
        let mut edges = HashSet::new();
        for (s, t) in self.edges.iter() {
            if !include_internals && t.id.is_internal() {
                for (_, t2) in self.edges.iter().filter(|(s2, _)| s2 == t) {
                    edges.insert((s, t2));
                }
            } else if include_internals || !s.id.is_internal() {
                edges.insert((s, t));
            }
        }
        NodeAndEdgeLists { nodes, edges }
    }

    /// Pare down a complete graph into only trace clocks, which is to
    /// say, only the interactions between probes.
    pub fn as_interactions<'a>(&'a self) -> NodeAndEdgeLists<&'a GraphEvent> {
        let mut node_set = HashSet::new();
        let mut edge_set = HashSet::new();
        self.filter(
            |n| node_set.insert((n.probe_id, n.clock)),
            |s, t| {
                s.probe_id != t.probe_id
                    && edge_set.insert(((s.probe_id, s.clock), (t.probe_id, t.clock)))
            },
        )
    }

    /// Pare down a complete graph into the event transitions.
    pub fn as_states<'a>(&'a self, include_internals: bool) -> NodeAndEdgeLists<&'a GraphEvent> {
        let mut nodes = HashMap::new();
        for n in self
            .nodes
            .iter()
            .filter(|n| include_internals || !n.id.is_internal())
        {
            nodes.insert((n.probe_id, n.id), n);
        }
        let mut edges = HashMap::new();
        for (s, t) in self.edges.iter() {
            if !include_internals && t.id.is_internal() {
                for (_, t2) in self.edges.iter().filter(|(s2, _)| s2 == t) {
                    edges.insert(((s.probe_id, s.id), (t2.probe_id, t2.id)), (s, t2));
                }
            } else if include_internals || !s.id.is_internal() {
                edges.insert(((s.probe_id, s.id), (t.probe_id, t.id)), (s, t));
            }
        }
        NodeAndEdgeLists {
            nodes: nodes.into_iter().map(|(_, v)| v).collect(),
            edges: edges.into_iter().map(|(_, v)| v).collect(),
        }
    }

    /// Pare down a complete graph into just the probes and their
    /// communication topology.
    pub fn as_topology<'a>(&'a self) -> NodeAndEdgeLists<&'a GraphEvent> {
        let mut node_set = HashSet::new();
        let mut edge_set = HashSet::new();
        self.filter(
            |n| node_set.insert(n.probe_id),
            |s, t| s.probe_id != t.probe_id && edge_set.insert((s.probe_id, t.probe_id)),
        )
    }

    fn filter<'a, NF, EF>(
        &'a self,
        mut node_filter: NF,
        mut edge_filter: EF,
    ) -> NodeAndEdgeLists<&'a GraphEvent>
    where
        NF: FnMut(&'a GraphEvent) -> bool,
        EF: FnMut(&'a GraphEvent, &'a GraphEvent) -> bool,
    {
        let nodes = self.nodes.iter().filter(|n| node_filter(n)).collect();

        let edges = self
            .edges
            .iter()
            .filter(|(s, t)| edge_filter(s, t))
            .map(|(s, t)| (s, t))
            .collect();
        NodeAndEdgeLists { nodes, edges }
    }

    pub fn probe_log<'a>(&'a self, probe_id: ProbeId) -> Vec<&'a GraphEvent> {
        let mut log = Vec::new();
        for (s, t) in self.edges.iter().filter(|(_, t)| t.probe_id == probe_id) {
            log.push((t, (t.clock.pack().1 as f32, t.seq, t.seq_idx)));
            // If the source of the edge was from a different probe,
            // collect the events from the corresponding segment and
            // add them to our log.
            if s.probe_id != probe_id {
                for nn in self
                    .nodes
                    .iter()
                    .filter(|n| n.clock == s.clock && n.probe_id == s.probe_id)
                {
                    // Neighbor segments are annotated with
                    // half-clocks so they end up inbetween local
                    // events in the log when it gets sorted. If a
                    // target has > 1 incoming edge from a neighbor,
                    // those are arbitrarily ordered by those
                    // neighbors' sequence numbers.
                    //
                    // NOTE: this is natural due to the nature of a
                    // poset, nodes from distinct timelines are not
                    // comparable.
                    log.push((nn, (t.clock.pack().1 as f32 - 0.5, nn.seq, nn.seq_idx)));
                }
            } else {
                // Otherwise, just insert the local source event.
                log.push((s, (s.clock.pack().1 as f32, s.seq, s.seq_idx)));
            }
        }
        log.sort_by(|a, b| {
            a.1.partial_cmp(&b.1)
                .expect("error: should be able to compare two floats")
        });
        // If a node has more than one incoming edge, it will appear
        // twice in the log, this unique-ifies the log.
        let mut log_set = HashSet::new();
        log.into_iter()
            .map(|(g, _)| g)
            .filter(|g| log_set.insert(*g))
            .collect()
    }
}

impl<'a> NodeAndEdgeLists<&'a GraphEvent> {
    pub fn dot(
        &self,
        cfg: &Cfg,
        name: &'static str,
        temp: &'static str,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let ctx = graph_to_tree(&self.nodes, &self.edges, cfg);
        let mut tt = TinyTemplate::new();
        tt.add_formatter(
            "discrete_color_formatter",
            templates::discrete_color_formatter,
        );
        tt.add_formatter(
            "gradient_color_formatter",
            templates::gradient_color_formatter,
        );
        tt.add_template(name, temp)?;
        Ok(tt.render(name, &ctx)?)
    }
}

impl Graph for NodeAndEdgeLists<GraphEvent> {
    fn add_node(&mut self, node: GraphEvent) {
        self.nodes.insert(node);
    }

    fn add_edge(&mut self, source: GraphEvent, target: GraphEvent) {
        self.edges.insert((source, target));
    }
}

fn graph_to_tree<'a>(
    nodes: &HashSet<&GraphEvent>,
    edges: &HashSet<(&GraphEvent, &GraphEvent)>,
    cfg: &'a Cfg,
) -> Context<'a> {
    let mut ctx = Context {
        components: ComponentSet::new(),
        edges: EdgeSet::new(),
    };

    let mut cluster_idx = 0;

    for node in nodes {
        let (comp_name, probe_meta) = if let Some(pmeta) = cfg.probes.get(&node.probe_id.get_raw())
        {
            let comp_id = pmeta.component_id.to_string();
            if let Some(cname) = cfg.component_names.get(&comp_id) {
                (cname.clone(), Some(pmeta))
            } else {
                (comp_id, Some(pmeta))
            }
        } else {
            ("UNKNOWN".to_string(), None)
        };
        let comp = ctx.components.entry(comp_name.clone()).or_insert_with(|| {
            cluster_idx += 1;
            Component {
                cluster_idx,
                name: comp_name,
                probes: ProbeSet::new(),
            }
        });
        let probe_name = format!("UNKNOWN_PROBE_{}", node.probe_id.get_raw());
        let probe = comp.probes.entry(probe_name.clone()).or_insert_with(|| {
            cluster_idx += 1;
            Probe {
                cluster_idx,
                name: probe_meta.map(|p| p.name.clone()).unwrap_or(probe_name),
                is_known: probe_meta.is_some(),
                meta: probe_meta,
                raw_id: node.probe_id.get_raw(),
                events: vec![],
            }
        });

        if let Ok(emeta) = meta::get_event_meta(cfg, &node.probe_id, &node.id) {
            let payload =
                meta::parsed_payload(emeta.type_hint.as_ref().map(|s| s.as_ref()), node.payload)
                    .unwrap_or(None);
            probe.events.push(Event {
                is_known: true,
                probe_name: probe.name.clone(),
                has_payload: payload.is_some(),
                payload,
                meta: Some(emeta),
                raw_id: node.id.get_raw(),
                raw_probe_id: node.probe_id.get_raw(),
                clock: node.clock.pack().1,
                seq: node.seq.0,
                seq_idx: node.seq_idx,
            });
        } else {
            probe.events.push(Event {
                is_known: false,
                probe_name: probe.name.clone(),
                meta: None,
                has_payload: false,
                payload: None,
                raw_id: node.id.get_raw(),
                raw_probe_id: node.probe_id.get_raw(),
                clock: node.clock.pack().1,
                seq: node.seq.0,
                seq_idx: node.seq_idx,
            });
        }
    }

    for (s, t) in edges {
        let from = {
            let probe_name = if let Some(pmeta) = cfg.probes.get(&s.probe_id.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", s.probe_id.get_raw())
            };
            if let Ok(emeta) = meta::get_event_meta(cfg, &s.probe_id, &s.id) {
                Event {
                    is_known: true,
                    probe_name: probe_name.clone(),
                    meta: Some(emeta),
                    raw_id: s.id.get_raw(),
                    raw_probe_id: s.probe_id.get_raw(),
                    seq: s.seq.0,
                    seq_idx: s.seq_idx,
                    clock: s.clock.pack().1,
                    // Payloads aren't needed for edge
                    // enumeration.
                    payload: None,
                    has_payload: false,
                }
            } else {
                Event {
                    is_known: false,
                    probe_name: probe_name.clone(),
                    meta: None,
                    raw_id: s.id.get_raw(),
                    raw_probe_id: s.probe_id.get_raw(),
                    seq: s.seq.0,
                    seq_idx: s.seq_idx,
                    clock: s.clock.pack().1,
                    // Payloads aren't needed for edge
                    // enumeration.
                    payload: None,
                    has_payload: false,
                }
            }
        };
        let to = {
            let probe_name = if let Some(pmeta) = cfg.probes.get(&t.probe_id.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", s.probe_id.get_raw())
            };
            if let Ok(emeta) = meta::get_event_meta(cfg, &t.probe_id, &t.id) {
                Event {
                    is_known: true,
                    probe_name: probe_name.clone(),
                    meta: Some(emeta),
                    raw_id: t.id.get_raw(),
                    raw_probe_id: t.probe_id.get_raw(),
                    seq: t.seq.0,
                    seq_idx: t.seq_idx,
                    clock: t.clock.pack().1,
                    // Payloads aren't needed for edge
                    // enumeration.
                    payload: None,
                    has_payload: false,
                }
            } else {
                Event {
                    is_known: false,
                    probe_name: probe_name.clone(),
                    meta: None,
                    raw_id: t.id.get_raw(),
                    raw_probe_id: t.probe_id.get_raw(),
                    seq: t.seq.0,
                    seq_idx: t.seq_idx,
                    clock: t.clock.pack().1,
                    // Payloads aren't needed for edge
                    // enumeration.
                    payload: None,
                    has_payload: false,
                }
            }
        };

        ctx.edges.insert(Edge { from, to });
    }
    ctx
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use uuid::Uuid;

    use modality_probe::{EventId, LogicalClock, ProbeEpoch, ProbeId, ProbeTicks};
    use modality_probe_collector_common::SequenceNumber;
    use modality_probe_graph::GraphEvent;

    use crate::meta::{Cfg, EventMeta, ProbeMeta};

    use super::super::templates;

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

    #[test]
    fn complete_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph
            .graph
            .as_complete(false)
            .dot(&cfg, "complete", templates::COMPLETE)
            .unwrap();
        assert!(dot.contains("one_one_1_0 ->\n    two_two_1_2"), dot);
    }

    #[test]
    fn interactions_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph
            .graph
            .as_interactions()
            .dot(&cfg, "interactions", templates::INTERACTIONS)
            .unwrap();
        assert!(dot.contains("one_0 -> two_1"), dot);
    }

    #[test]
    fn states_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph
            .graph
            .as_states(false)
            .dot(&cfg, "states", templates::STATES)
            .unwrap();
        assert!(dot.contains("one_AT_one ->\n    two_AT_two"), dot);
    }

    #[test]
    fn topo_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph
            .graph
            .as_topology()
            .dot(&cfg, "topo", templates::TOPO)
            .unwrap();
        assert!(dot.contains("one -> two"), dot);
    }

    #[test]
    fn probe_log() {
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();
        let expected_perm1 = vec![
            GraphEvent {
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
            },
            GraphEvent {
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
            },
            GraphEvent {
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
            },
        ];
        let expected_perm2 = vec![
            GraphEvent {
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
            },
            GraphEvent {
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
            },
            GraphEvent {
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
            },
        ];
        assert!(
            graph.graph.probe_log(ProbeId::new(4).unwrap())
                == expected_perm1.iter().map(|g| g).collect::<Vec<_>>()
                || graph.graph.probe_log(ProbeId::new(4).unwrap())
                    == expected_perm2.iter().map(|g| g).collect::<Vec<_>>()
        );
    }
}
