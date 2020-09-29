use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    iter::Peekable,
};

use serde::{Deserialize, Serialize};
use tinytemplate::TinyTemplate;
use uuid::Uuid;

use modality_probe::{EventId, ProbeId};
use modality_probe_collector_common::{ReportIter, ReportLogEntry};
use modality_probe_graph::{EventDigraph, Graph, GraphEvent};

use super::{
    templates::{self, Component, ComponentSet, Context, Edge, EdgeSet, Event, Probe, ProbeSet},
    {Cfg, ExportError},
};

/// A row in the events.csv for a component.
#[derive(PartialEq, Eq, Debug, Clone, Deserialize, Hash, Serialize)]
pub struct EventMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub type_hint: Option<String>,
    pub tags: String,
    pub description: String,
    pub file: String,
    pub line: String,
}

/// A row in probes.csv for a component.
#[derive(PartialEq, Serialize, Debug, Clone, Deserialize)]
pub struct ProbeMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub line: String,
}

pub(super) fn log_to_graph<I>(
    log: Peekable<I>,
) -> Result<EventDigraph<NodeAndEdgeLists<GraphEvent>>, ExportError>
where
    I: Iterator<Item = ReportLogEntry>,
{
    let mut graph = EventDigraph::new(NodeAndEdgeLists {
        nodes: HashSet::new(),
        edges: HashSet::new(),
    });
    let report_iter = ReportIter::new(log);
    for report in report_iter {
        graph.add_report(&report).map_err(|e| {
            ExportError(format!(
                "encountered an error reconstructing the graph: {}",
                e
            ))
        })?;
    }
    Ok(graph)
}

#[derive(Default)]
pub(super) struct NodeAndEdgeLists<G>
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
        let nodes = self
            .nodes
            .iter()
            .filter(|n| node_filter(n))
            .map(|n| n)
            .collect();

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
            if s.probe_id != probe_id {
                for nn in self
                    .nodes
                    .iter()
                    .filter(|n| n.clock == s.clock && n.probe_id == s.probe_id)
                {
                    log.push((nn, (t.clock.pack().1 as f32 - 0.5, nn.seq, nn.seq_idx)));
                }
            } else {
                log.push((s, (s.clock.pack().1 as f32, s.seq, s.seq_idx)));
                log.push((t, (t.clock.pack().1 as f32, t.seq, t.seq_idx)));
            }
        }
        log.sort_by(|a, b| {
            a.1.partial_cmp(&b.1)
                .expect("error: should be able to compare two floats")
        });
        log.into_iter().map(|(g, _)| g).collect()
    }
}

impl<'a> NodeAndEdgeLists<&'a GraphEvent> {
    pub fn dot(
        &self,
        cfg: &Cfg,
        name: &'static str,
        temp: &'static str,
    ) -> Result<String, ExportError> {
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
        tt.add_template(name, temp).unwrap();
        Ok(tt.render(name, &ctx).unwrap())
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

pub fn get_event_meta<'a>(
    cfg: &'a Cfg,
    pid: &ProbeId,
    eid: &EventId,
) -> Result<&'a EventMeta, ExportError> {
    let comp_id = cfg
        .probes_to_components
        .get(&pid.get_raw())
        .ok_or_else(|| {
            ExportError(format!(
                "unable to find a matching component for probe {}",
                pid.get_raw()
            ))
        })?;
    Ok(cfg.events.get(&(*comp_id, eid.get_raw())).ok_or_else(|| {
        ExportError(format!(
            "unable to find metadata for event {} in component {}",
            eid.get_raw(),
            comp_id
        ))
    })?)
}

pub fn parsed_payload(th: &str, pl: u32) -> Result<String, ExportError> {
    match th {
        "i8" => Ok(format!("{}", pl as i8)),
        "i16" => Ok(format!("{}", pl as i16)),
        "i32" => Ok(format!("{}", pl as i32)),
        "u8" => Ok(format!("{}", pl as u8)),
        "u16" => Ok(format!("{}", pl as u16)),
        "u32" => Ok(format!("{}", pl as u32)),
        "f32" => Ok(format!("{}", pl as f32)),
        "bool" => Ok(format!("{}", pl != 0)),
        _ => Err(ExportError(format!("{} is not a valid type hint", th))),
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

        if let Ok(emeta) = get_event_meta(cfg, &node.probe_id, &node.id) {
            let payload = node.payload.and_then(|pl| {
                emeta
                    .type_hint
                    .as_ref()
                    .and_then(|th| parsed_payload(&th, pl).ok())
            });
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
            if let Ok(emeta) = get_event_meta(cfg, &s.probe_id, &s.id) {
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
            if let Ok(emeta) = get_event_meta(cfg, &t.probe_id, &t.id) {
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

    use super::{super::templates, *};

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
}
