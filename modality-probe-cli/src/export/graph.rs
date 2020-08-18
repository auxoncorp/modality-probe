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
            if s.probe_id != t.probe_id {
                let weight = edges
                    .entry(((s.probe_id, s.clock), (t.probe_id, t.clock)))
                    .or_insert(0);
                *weight += 1;
            }
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
            if s.probe_id != t.probe_id {
                let weight = edges.entry((s.probe_id, t.probe_id)).or_insert(0);
                *weight += 1;
            }
        }

        NodeAndEdgeLists { nodes, edges }
    }

    /// Spit out a string containing dot code representing a complete
    /// graph.
    pub fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
        let mut out = String::new();
        writeln!(out, "digraph G {{")?;
        for (node, _) in self.nodes.iter() {
            let pname = if let Some(pmeta) = cfg.probes.get(&node.probe_id.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", node.probe_id.get_raw())
            };
            if let Ok(emeta) = get_event_meta(cfg, &node.probe_id, &node.id) {
                write!(out, "    {}_{}_{} [ ", emeta.name, node.seq.0, node.seq_idx)?;
                write!(
                out,
                "label = \"{}\" description = \"{}\" file = \"{}\" {} probe = \"{}\" tags = \"{}\" raw_event_id = {} raw_probe_id = {} ",
                emeta.name,
                emeta.description,
                emeta.file,
                if emeta.line.is_empty() {
                    String::new()
                } else {
                    format!("line = {}", emeta.line)
                },
                pname,
                emeta.tags,
                node.id.get_raw(),
                node.probe_id.get_raw()
            )?;
                if let Some(pl) = node.payload {
                    if let Some(ref th) = emeta.type_hint {
                        write!(out, "payload = {} ", parsed_payload(th, pl)?)?;
                    }
                }
                write!(out, " ]\n")?;
            } else {
                writeln!(
                    out,
                    "    UNKNOWN_EVENT_{}_{}_{} [ label = \"UNKNOWN_EVENT_{}\" raw_event_id = {} probe = \"{}\" raw_probe_id = {} ]",
                    node.id.get_raw(),
                    node.seq.0,
                    node.seq_idx,
                    node.id.get_raw(),
                    node.id.get_raw(),
                    pname,
                    node.probe_id.get_raw()
                )?;
            }
        }

        for ((s, t), _) in self.edges.iter() {
            let source_name = if let Ok(meta) = get_event_meta(cfg, &s.probe_id, &s.id) {
                meta.name.clone()
            } else {
                format!("UNKNOWN_EVENT_{}", s.id.get_raw())
            };
            let target_name = if let Ok(meta) = get_event_meta(cfg, &t.probe_id, &t.id) {
                meta.name.clone()
            } else {
                format!("UNKNOWN_EVENT_{}", t.id.get_raw())
            };
            writeln!(
                out,
                "    {}_{}_{} -> {}_{}_{}",
                source_name, s.seq.0, s.seq_idx, target_name, t.seq.0, t.seq_idx
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
            if let Some(pmeta) = cfg.probes.get(&probe.get_raw()) {
                writeln!(
                out,
                "    {}_{} [ label = \"{}\" description = \"{}\" file = \"{}\" {} raw_probe_id = {} weight = {} ]",
                pmeta.name,
                modality_probe::pack_clock_word(clock.epoch, clock.ticks),
                pmeta.name,
                pmeta.description,
                pmeta.file,
                if pmeta.line.is_empty() {
                    String::new()
                } else {
                    format!("line = {}", pmeta.line)
                },
                probe.get_raw(),
                w
            )?;
            } else {
                writeln!(
                    out,
                    "    UNKNOWN_PROBE_{}_{} [ label = \"UNKNOWN_PROBE_{}\" raw_probe_id = {} ]",
                    probe.get_raw(),
                    modality_probe::pack_clock_word(clock.epoch, clock.ticks),
                    probe.get_raw(),
                    probe.get_raw(),
                )?;
            }
        }

        for (((sprobe, sclock), (tprobe, tclock)), _) in self.edges.iter() {
            let source_name = if let Some(meta) = cfg.probes.get(&sprobe.get_raw()) {
                meta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", sprobe.get_raw())
            };
            let target_name = if let Some(meta) = cfg.probes.get(&tprobe.get_raw()) {
                meta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", tprobe.get_raw())
            };
            writeln!(
                out,
                "    {}_{} -> {}_{}",
                source_name,
                modality_probe::pack_clock_word(sclock.epoch, sclock.ticks),
                target_name,
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
            let pname = if let Some(pmeta) = cfg.probes.get(&pid.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", pid.get_raw())
            };
            if let Ok(emeta) = get_event_meta(&cfg, pid, eid) {
                writeln!(
                    out,
                    "    {}_AT_{} [ label = \"{} @ {}\" description = \"{}\" file = \"{}\" {} tags = \"{}\" raw_event_id = {} weight = {} ]",
                    emeta.name,
                    pname,
                    emeta.name,
                    pname,
                    emeta.description,
                    emeta.file,
                    if emeta.line.is_empty() {
                        String::new()
                    } else {
                        format!("line = {}", emeta.line)
                    },
                    emeta.tags,
                    eid.get_raw(),
                    w
                )?;
            } else {
                writeln!(
                    out,
                    "UNKNOWN_EVENT_{}_AT_{} [ label = \"UNKNOWN_EVENT_{} @ {}\" raw_event_id = {} raw_probe_id = {} ]",
                    eid.get_raw(),
                    pname,
                    eid.get_raw(),
                    pname,
                    eid.get_raw(),
                    pid.get_raw(),
                )?;
            }
        }

        for (((sp, se), (tp, te)), w) in self.edges.iter() {
            let source_probe = if let Some(pmeta) = cfg.probes.get(&sp.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", sp.get_raw())
            };
            let source_event = if let Ok(emeta) = get_event_meta(&cfg, sp, se) {
                emeta.name.clone()
            } else {
                format!("UNKNOWN_EVENT_{}", se.get_raw())
            };
            let target_probe = if let Some(pmeta) = cfg.probes.get(&tp.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", tp.get_raw())
            };
            let target_event = if let Ok(emeta) = get_event_meta(&cfg, sp, te) {
                emeta.name.clone()
            } else {
                format!("UNKNOWN_EVENT_{}", te.get_raw())
            };
            writeln!(
                out,
                "    {}_AT_{} -> {}_AT_{} [ weight = {} ]",
                source_event, source_probe, target_event, target_probe, w
            )?;
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
            if let Some(pmeta) = cfg.probes.get(&node.get_raw()) {
                writeln!(out, "    {} [ label = \"{}\" description = \"{}\" file = \"{}\" line = {} raw_probe_id = {} weight = {} ]",
                pmeta.name,
                pmeta.name,
                pmeta.description,
                pmeta.file,
                pmeta.line,
                node.get_raw(),
                w
            )?;
            } else {
                writeln!(
                    out,
                    "    UNKNOWN_PROBE_{} [ label = \"UNKNOWN_PROBE_{}\" ]",
                    node.get_raw(),
                    node.get_raw()
                )?;
            }
        }

        for ((s, t), w) in self.edges.iter() {
            let source_name = if let Some(pmeta) = cfg.probes.get(&s.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", s.get_raw())
            };
            let target_name = if let Some(pmeta) = cfg.probes.get(&t.get_raw()) {
                pmeta.name.clone()
            } else {
                format!("UNKNOWN_PROBE_{}", t.get_raw())
            };
            writeln!(
                out,
                "    {} -> {} [ weight = {} ]",
                source_name, target_name, w,
            )?;
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
