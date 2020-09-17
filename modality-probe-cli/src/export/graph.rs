use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    hash::Hash,
    iter::Peekable,
    ops::Deref,
};

use colorous::{Color, Gradient};
use serde::{Deserialize, Serialize};
use tinytemplate::TinyTemplate;
use uuid::Uuid;

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{ReportIter, ReportLogEntry};
use modality_probe_graph::{EventDigraph, Graph, GraphEvent};

use super::{
    templates::{Component, ComponentSet, EdgeSet, Probe, ProbeSet},
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
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub(super) struct ProbeMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub line: String,
}

pub(super) fn log_to_graph<I>(
    log: Peekable<I>,
) -> Result<EventDigraph<NodeAndEdgeLists<GraphEvent, ()>>, ExportError>
where
    I: Iterator<Item = ReportLogEntry>,
{
    let mut graph = EventDigraph::new(NodeAndEdgeLists {
        nodes: HashMap::new(),
        edges: HashMap::new(),
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
pub(super) struct NodeAndEdgeLists<G, NW = (), EW = ()> {
    nodes: HashMap<G, NW>,
    edges: HashMap<(G, G), EW>,
}

impl<G> NodeAndEdgeLists<G>
where
    G: Deref<Target = GraphEvent> + Hash + Eq,
{
    pub fn filter<'a, NF, EF>(&'a self, node_filter: NF, edge_filter: EF) -> NodeAndEdgeLists<&'a G>
    where
        NF: Fn(&'a G) -> bool,
        EF: Fn(&'a G, &'a G) -> bool,
    {
        let nodes = self
            .nodes
            .iter()
            .filter(|(n, _)| node_filter(n))
            .map(|(n, _)| (n, ()))
            .collect();

        let edges = self
            .edges
            .iter()
            .filter(|((s, t), _)| edge_filter(s, t))
            .map(|((s, t), _)| ((s, t), ()))
            .collect();
        NodeAndEdgeLists { nodes, edges }
    }

    /// Pare down a complete graph into only trace clocks, which is to
    /// say, only the interactions between probes.
    pub fn as_interactions<'a>(&'a self) -> NodeAndEdgeLists<&'a G> {
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
    pub fn into_states<'a>(&'a self) -> NodeAndEdgeLists<&'a G> {
        let mut node_set = HashSet::new();
        let mut edge_set = HashSet::new();
        self.filter(
            |n| node_set.insert((n.probe_id, n.id)),
            |s, t| edge_set.insert(((s.probe_id, s.id), (t.probe_id, t.id))),
        )
    }

    /// Pare down a complete graph into just the probes and their
    /// communication topology.
    pub fn into_topology<'a>(&'a self) -> NodeAndEdgeLists<&'a G> {
        let mut node_set = HashSet::new();
        let mut edge_set = HashSet::new();
        self.filter(
            |n| node_set.insert(n.probe_id),
            |s, t| edge_set.insert((s.probe_id, t.probe_id)),
        )
    }

    /// Spit out a string containing dot code representing a complete
    /// graph.
    pub fn to_dot(
        &self,
        cfg: &Cfg,
        name: &'static str,
        temp: &'static str,
    ) -> Result<String, ExportError> {
        let ctx = graph_to_tree(
            self.nodes.keys().map(Deref::deref),
            self.edges.keys().map(|(s, t)| (s.deref(), t.deref())),
            cfg,
        );
        let mut tt = TinyTemplate::new();
        tt.add_template(name, temp).unwrap();
        Ok(tt.render(name, &ctx).unwrap())
    }
}

impl Graph for NodeAndEdgeLists<GraphEvent, ()> {
    fn add_node(&mut self, node: GraphEvent) {
        self.nodes.insert(node, ());
    }

    fn add_edge(&mut self, source: GraphEvent, target: GraphEvent) {
        self.edges.insert((source, target), ());
    }
}

fn get_event_meta<'a>(
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

fn parsed_payload(th: &str, pl: u32) -> Result<String, ExportError> {
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

struct Palette<C, S> {
    cursor: C,
    set: S,
}

impl Palette<f64, Gradient> {
    fn new(set: Gradient) -> Self {
        Palette { cursor: 0.0, set }
    }

    fn next(&mut self) -> Color {
        self.cursor = (self.cursor + 0.1) % 1.0;
        self.set.eval_continuous(self.cursor)
    }
}

impl Palette<usize, [Color; 10]> {
    fn new(set: [Color; 10]) -> Self {
        Palette { cursor: 0, set }
    }

    fn next(&mut self) -> Color {
        self.cursor = (self.cursor + 1) % 10;
        self.set[self.cursor]
    }
}

use super::templates::complete::Context;

fn graph_to_tree<'a>(
    nodes: impl Iterator<Item = &'a GraphEvent>,
    edges: impl Iterator<Item = (&'a GraphEvent, &'a GraphEvent)>,
    cfg: &Cfg,
) -> Context {
    use crate::export::templates::complete::*;

    let mut ctx = Context {
        components: ComponentSet::new(),
        edges: EdgeSet::new(),
    };

    let mut cluster_idx = 0;

    for node in nodes {
        let probe = update_comps_and_probes(node, &mut ctx.components, &cfg, &mut cluster_idx);

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
                meta: Some(emeta.clone()),
                raw_id: node.id.get_raw(),
                raw_probe_id: node.probe_id.get_raw(),
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
                    meta: Some(emeta.clone()),
                    raw_id: s.id.get_raw(),
                    raw_probe_id: s.probe_id.get_raw(),
                    seq: s.seq.0,
                    seq_idx: s.seq_idx,
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
                    meta: Some(emeta.clone()),
                    raw_id: t.id.get_raw(),
                    raw_probe_id: t.probe_id.get_raw(),
                    seq: t.seq.0,
                    seq_idx: t.seq_idx,
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

fn update_comps_and_probes<'a, E: Serialize>(
    node: &'a GraphEvent,
    comps: &'a mut ComponentSet<E>,
    cfg: &Cfg,
    cluster_idx: &mut usize,
) -> &'a mut Probe<E> {
    let mut comp_palette = Palette::<_, Gradient>::new(colorous::GREYS);
    let mut probe_palette = Palette::<_, [Color; 10]>::new(colorous::TABLEAU10);

    let (comp_name, probe_name) = if let Some(pmeta) = cfg.probes.get(&node.probe_id.get_raw()) {
        let comp_id = pmeta.component_id.to_string();
        if let Some(cname) = cfg.component_names.get(&comp_id) {
            (cname.clone(), pmeta.name.clone())
        } else {
            (comp_id, pmeta.name.clone())
        }
    } else {
        (
            "UNKNOWN".to_string(),
            format!("UNKNOWN_PROBE_{}", node.probe_id.get_raw()),
        )
    };
    let comp = comps.entry(comp_name.clone()).or_insert_with(|| {
        *cluster_idx += 1;
        Component {
            cluster_idx: *cluster_idx,
            name: comp_name,
            fill_color: format!("#{:x}", comp_palette.next()),
            probes: ProbeSet::new(),
        }
    });
    let probe = comp.probes.entry(probe_name.clone()).or_insert_with(|| {
        *cluster_idx += 1;
        Probe {
            cluster_idx: *cluster_idx,
            name: probe_name.clone(),
            raw_id: node.probe_id.get_raw(),
            fill_color: format!("#{:x}", probe_palette.next()),
            events: vec![],
        }
    });
    probe
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

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

        let dot = graph.graph.to_dot(&cfg).unwrap();
        assert!(dot.contains("one_one_1_0 -> two_two_1_2"), dot);
    }

    // #[test]
    // fn interactions_dot() {
    //     let cfg = cfg();
    //     let diamond_log = modality_probe_graph::test_support::diamond()
    //         .into_iter()
    //         .map(|e| (&e).try_into().unwrap())
    //         .peekable();
    //     let graph = super::log_to_graph(diamond_log).unwrap();

    //     let dot = graph.graph.into_interactions().to_dot(&cfg).unwrap();
    //     assert!(dot.contains("one_0 -> two_1"), dot);
    // }

    // #[test]
    // fn states_dot() {
    //     let cfg = cfg();
    //     let diamond_log = modality_probe_graph::test_support::diamond()
    //         .into_iter()
    //         .map(|e| (&e).try_into().unwrap())
    //         .peekable();
    //     let graph = super::log_to_graph(diamond_log).unwrap();

    //     let dot = graph.graph.into_states().to_dot(&cfg).unwrap();
    //     assert!(dot.contains("one -> two"), dot);
    // }

    // #[test]
    // fn topo_dot() {
    //     let cfg = cfg();
    //     let diamond_log = modality_probe_graph::test_support::diamond()
    //         .into_iter()
    //         .map(|e| (&e).try_into().unwrap())
    //         .peekable();
    //     let graph = super::log_to_graph(diamond_log).unwrap();

    //     let dot = graph.graph.into_topology().to_dot(&cfg).unwrap();
    //     assert!(dot.contains("one -> two"), dot);
    // }

    #[test]
    fn palette_doesnt_panic() {
        let mut p = Palette::<f64, _>::new(colorous::CUBEHELIX);
        for _ in 0..20 {
            p.next();
        }
        let mut p = Palette::<usize, _>::new(colorous::TABLEAU10);
        for _ in 0..20 {
            p.next();
        }
    }
}
