use std::{collections::HashMap, fmt::Write, iter::Peekable};

use serde::Deserialize;
use uuid::Uuid;

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::{ReportIter, ReportLogEntry};
use modality_probe_graph::{EventDigraph, Graph, GraphEvent};

use super::{Cfg, ExportError};

/// A row in the events.csv for a component.
#[derive(PartialEq, Debug, Clone, Deserialize)]
pub(super) struct EventMeta {
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
pub(super) struct NodeAndEdgeLists<G, W> {
    nodes: HashMap<G, W>,
    edges: HashMap<(G, G), W>,
}

impl NodeAndEdgeLists<GraphEvent, ()> {
    /// pare down a complete graph into only trace clocks, which is to
    /// say, only the interactions between probes.
    pub fn into_interactions(self) -> NodeAndEdgeLists<(ProbeId, LogicalClock), u32> {
        let mut nodes = HashMap::new();
        for (n, _) in self.nodes.into_iter() {
            let weight = nodes.entry((n.probe_id, n.clock)).or_insert(0);
            *weight += 1;
        }

        let mut edges = HashMap::new();
        for ((s, t), _) in self.edges.into_iter() {
            let weight = edges
                .entry(((s.probe_id, s.clock), (t.probe_id, t.clock)))
                .or_insert(0);
            *weight += 1;
        }
        NodeAndEdgeLists { nodes, edges }
    }

    /// Pare down a complete graph into the event transitions.
    pub fn into_states(self) -> NodeAndEdgeLists<(ProbeId, EventId), u32> {
        let mut nodes = HashMap::new();
        for (n, _) in self.nodes.into_iter() {
            let weight = nodes.entry((n.probe_id, n.id)).or_insert(0);
            *weight += 1;
        }

        let mut edges = HashMap::new();
        for ((s, t), _) in self.edges.into_iter() {
            let weight = edges
                .entry(((s.probe_id, s.id), (t.probe_id, t.id)))
                .or_insert(0);
            *weight += 1;
        }

        NodeAndEdgeLists { nodes, edges }
    }

    /// Pare down a complete graph into just the probes and their
    /// communication topology.
    pub fn into_topology(self) -> NodeAndEdgeLists<ProbeId, u32> {
        let mut nodes = HashMap::new();
        for (n, _) in self.nodes.into_iter() {
            let weight = nodes.entry(n.probe_id).or_insert(0);
            *weight += 1;
        }

        let mut edges = HashMap::new();
        for ((s, t), _) in self.edges.into_iter() {
            let weight = edges.entry((s.probe_id, t.probe_id)).or_insert(0);
            *weight += 1;
        }

        NodeAndEdgeLists { nodes, edges }
    }

    /// Spit out a string containing dot code representing a complete
    /// graph.
    pub fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
        let mut out = String::new();
        writeln!(out, "digraph G {{")?;
        for (node, _) in self.nodes.iter() {
            let pmeta = cfg.probes.get(&node.probe_id.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    node.probe_id.get_raw(),
                ))
            })?;
            let emeta = get_event_meta(cfg, &node.probe_id, &node.id)?;
            write!(out, "{}_{}_{} [ ", emeta.name, node.seq.0, node.seq_idx)?;
            write!(
                out,
                "label = \"{}\" description = \"{}\" file = \"{}\" line = {} probe = \"{}\" tags = \"{}\" raw_event_id = {} raw_probe_id = {}\" ",
                emeta.name,
                emeta.description,
                emeta.file,
                emeta.line,
                pmeta.name,
                emeta.tags,
                node.id.get_raw(),
                node.probe_id.get_raw()
            )?;
            if let Some(pl) = node.payload {
                if let Some(ref th) = emeta.type_hint {
                    write!(out, "payload = {} ", parsed_payload(th, pl)?)?;
                }
            }
            write!(out, " ]\n\n")?;
        }

        for ((s, t), _) in self.edges.iter() {
            let smeta = get_event_meta(cfg, &s.probe_id, &s.id)?;
            let tmeta = get_event_meta(cfg, &t.probe_id, &t.id)?;
            writeln!(
                out,
                "{}_{}_{} -> {}_{}_{}",
                smeta.name, s.seq.0, s.seq_idx, tmeta.name, t.seq.0, t.seq_idx
            )?;
        }

        writeln!(out, "}}")?;
        Ok(out)
    }
}

impl NodeAndEdgeLists<(ProbeId, LogicalClock), u32> {
    /// Spit out dot code representing an interaction graph.
    pub fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
        let mut out = String::new();
        writeln!(out, "digraph G {{")?;
        for ((probe, clock), w) in self.nodes.iter() {
            let pmeta = cfg.probes.get(&probe.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    probe.get_raw()
                ))
            })?;
            write!(
                out,
                "{}_{} [ ",
                pmeta.name,
                modality_probe::pack_clock_word(clock.epoch, clock.ticks)
            )?;
            write!(
                out,
                "label = \"{}\" description = \"{}\" file = \"{}\" line = {} raw_probe_id = {}\" weight = {}",
                pmeta.name,
                pmeta.description,
                pmeta.file,
                pmeta.line,
                probe.get_raw(),
                w
            )?;
            write!(out, " ]\n\n")?;
        }

        for (((sprobe, sclock), (tprobe, tclock)), _) in self.edges.iter() {
            let smeta = cfg.probes.get(&sprobe.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    sprobe.get_raw()
                ))
            })?;
            let tmeta = cfg.probes.get(&tprobe.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    tprobe.get_raw()
                ))
            })?;
            writeln!(
                out,
                "{}_{} -> {}_{}",
                smeta.name,
                modality_probe::pack_clock_word(sclock.epoch, sclock.ticks),
                tmeta.name,
                modality_probe::pack_clock_word(tclock.epoch, tclock.ticks)
            )?;
        }

        writeln!(out, "}}")?;
        Ok(out)
    }
}

impl NodeAndEdgeLists<(ProbeId, EventId), u32> {
    /// Spit out dot code representing an event transition state
    /// machine.
    pub fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
        let mut out = String::new();
        writeln!(out, "digraph G {{")?;
        for ((pid, eid), w) in self.nodes.iter() {
            let emeta = get_event_meta(&cfg, pid, eid)?;
            write!(out, "{} [ ", emeta.name)?;
            write!(
                out,
                "[ label = \"{}\" description = \"{}\" file = \"{}\" line = {} tags = \"{}\" raw_event_id = {} weight = {} ]\n\n",
                emeta.name,
                emeta.description,
                emeta.file,
                emeta.line,
                emeta.tags,
                eid.get_raw(),
                w
            )?;
        }

        for (((sp, se), (tp, te)), _) in self.edges.iter() {
            let smeta = get_event_meta(&cfg, sp, se)?;
            let tmeta = get_event_meta(&cfg, tp, te)?;
            writeln!(out, "{} -> {}", smeta.name, tmeta.name)?;
        }

        writeln!(out, "}}")?;
        Ok(out)
    }
}

impl NodeAndEdgeLists<ProbeId, u32> {
    /// Spit out dot code representing a topology graph.
    pub fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
        let mut out = String::new();
        writeln!(out, "digraph G {{")?;
        for (node, w) in self.nodes.iter() {
            let pmeta = cfg.probes.get(&node.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    node.get_raw()
                ))
            })?;
            write!(out, "{} [ \"label = \"{}\" description = \"{}\" file = \"{}\" line = {} raw_probe_id = {} weight = {} ]",
                   pmeta.name,
                pmeta.name,
                pmeta.description,
                pmeta.file,
                pmeta.line,
                node.get_raw(),
                w
            )?;
        }

        for ((s, t), w) in self.edges.iter() {
            let smeta = cfg.probes.get(&s.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    s.get_raw()
                ))
            })?;
            let tmeta = cfg.probes.get(&t.get_raw()).ok_or_else(|| {
                ExportError(format!(
                    "unable to find metadata for probe id {}",
                    t.get_raw()
                ))
            })?;
            writeln!(out, "{} -> {} [ weight = {} ]", smeta.name, tmeta.name, w)?;
        }

        writeln!(out, "}}")?;
        Ok(out)
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
        assert!(dot.contains("one_1_0 -> two_1_2"), dot);
    }

    #[test]
    fn interactions_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph.graph.into_interactions().to_dot(&cfg).unwrap();
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

        let dot = graph.graph.into_states().to_dot(&cfg).unwrap();
        assert!(dot.contains("one -> two"), dot);
    }

    #[test]
    fn topo_dot() {
        let cfg = cfg();
        let diamond_log = modality_probe_graph::test_support::diamond()
            .into_iter()
            .map(|e| (&e).try_into().unwrap())
            .peekable();
        let graph = super::log_to_graph(diamond_log).unwrap();

        let dot = graph.graph.into_topology().to_dot(&cfg).unwrap();
        assert!(dot.contains("one -> two"), dot);
    }
}
