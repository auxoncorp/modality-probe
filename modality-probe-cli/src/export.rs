//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{collections::HashMap, fmt, fmt::Write, path::PathBuf, str::FromStr};

use err_derive::Error;
use structopt::StructOpt;
use uuid::Uuid;

use modality_probe::{EventId, LogicalClock, ProbeId};
use modality_probe_collector_common::ReportIter;
use modality_probe_graph::{EventDigraph, Graph, GraphEvent};

use crate::{
    component::Component,
    events::Events,
    graph::{EventMeta, ProbeMeta},
};

/// Export a textual representation of a causal graph using the
/// collected coumnar form as input.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Export {
    /// Generate the graph showing only the causal relationships,
    /// eliding the events inbetween.
    #[structopt(short, long)]
    pub interactions_only: bool,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub components: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
    /// The type of graph to output.
    ///
    /// This can be either `cyclic` or `acyclic`.
    ///
    /// * A cyclic graph is one which shows the possible paths from
    /// either an event or a probe.
    ///
    /// * An acyclic graph shows the causal history of either all
    /// events or the interactions between traces in the system.
    #[structopt(required = true)]
    pub graph_type: GraphType,
}

#[derive(Debug, PartialEq, StructOpt)]
pub enum GraphType {
    Cyclic,
    Acyclic,
}

impl FromStr for GraphType {
    type Err = ExportError;
    fn from_str(s: &str) -> Result<Self, ExportError> {
        match s {
            "cyclic" => Ok(GraphType::Cyclic),
            "acyclic" => Ok(GraphType::Acyclic),
            _ => Err(ExportError(format!("{} is not a valid graph type", s))),
        }
    }
}

#[derive(Debug, Error)]
#[error(display = "{}", _0)]
pub struct ExportError(String);

impl From<fmt::Error> for ExportError {
    fn from(e: fmt::Error) -> Self {
        ExportError(format!("encountered an error generating dot: {}", e))
    }
}

pub fn run(mut exp: Export) -> Result<(), ExportError> {
    let cfg = assemble_components(&mut exp.components)?;
    let mut lrdr = csv::Reader::from_path(&exp.report).map_err(|e| {
        ExportError(format!(
            "failed to open the report file at {}: {}",
            exp.report.display(),
            e
        ))
    })?;
    let mut graph = EventDigraph::new(NodeAndEdgeLists {
        nodes: HashMap::new(),
        edges: HashMap::new(),
    });
    let report_iter = ReportIter::new(lrdr.deserialize().peekable());
    for report in report_iter {
        graph
            .add_report(&report.map_err(|e| {
                ExportError(format!(
                    "encountered an error deserializing the report: {}",
                    e
                ))
            })?)
            .map_err(|e| {
                ExportError(format!(
                    "encountered an error reconstructing the graph: {}",
                    e
                ))
            })?;
    }

    let mut out = String::new();
    writeln!(out, "Digraph G {{")?;

    match (exp.graph_type, exp.interactions_only) {
        (GraphType::Acyclic, false) => println!("{}", graph.graph.to_dot(&cfg)?),
        (GraphType::Acyclic, true) => println!("{}", graph.graph.into_interactions().to_dot(&cfg)?),
        (GraphType::Cyclic, false) => println!("{}", graph.graph.into_states().to_dot(&cfg)?),
        (GraphType::Cyclic, true) => println!("{}", graph.graph.into_topology().to_dot(&cfg)?),
    }

    Ok(())
}

#[derive(Default)]
struct NodeAndEdgeLists<G, W> {
    nodes: HashMap<G, W>,
    edges: HashMap<(G, G), W>,
}

impl NodeAndEdgeLists<GraphEvent, ()> {
    fn into_interactions(self) -> NodeAndEdgeLists<(ProbeId, LogicalClock), u32> {
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

    fn into_states(self) -> NodeAndEdgeLists<(ProbeId, EventId), u32> {
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

    fn into_topology(self) -> NodeAndEdgeLists<ProbeId, u32> {
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

    fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
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
            let tmeta = get_event_meta(cfg, &t.probe_id, &s.id)?;
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
    fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
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
    fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
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
    fn to_dot(&self, cfg: &Cfg) -> Result<String, ExportError> {
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

struct Cfg {
    pub probes: HashMap<u32, ProbeMeta>,
    pub events: HashMap<(Uuid, u32), EventMeta>,
    pub probes_to_components: HashMap<u32, Uuid>,
}

fn assemble_components(comp_dirs: &mut Vec<PathBuf>) -> Result<Cfg, ExportError> {
    let mut probes = HashMap::new();
    let mut probes_to_components = HashMap::new();
    let mut events = HashMap::new();

    let mut event_files = Vec::new();
    let mut probe_files = Vec::new();
    for dir in comp_dirs.iter_mut() {
        dir.push("probes.csv");
        probe_files.push(dir.clone());
        dir.pop();
        dir.push("events.csv");
        event_files.push(dir.clone());
    }
    for pf in probe_files.iter_mut() {
        let mut pr_rdr = csv::Reader::from_path(pf.clone()).map_err(|e| {
            ExportError(format!(
                "failed to open the probes file at {}: {}",
                pf.display(),
                e
            ))
        })?;
        for res in pr_rdr.deserialize() {
            let p: ProbeMeta =
                res.map_err(|e| ExportError(format!("failed to deserialize a probe row: {}", e)))?;
            pf.pop();
            pf.push("Component.toml");
            let comp = Component::from_toml(&pf);
            probes.insert(p.id, p.clone());
            probes_to_components.insert(p.id, comp.id.0);
        }
    }
    for ef in event_files.iter_mut() {
        let mut ev_rdr = csv::Reader::from_path(ef.clone()).map_err(|e| {
            ExportError(format!(
                "failed to open the events file at {}: {}",
                ef.display(),
                e
            ))
        })?;
        for res in ev_rdr.deserialize() {
            let e: EventMeta =
                res.map_err(|e| ExportError(format!("failed to deserialize a event row: {}", e)))?;
            ef.pop();
            ef.push("Component.toml");
            let comp = Component::from_toml(&ef);
            events.insert((comp.id.0, e.id), e.clone());
        }
    }

    add_internal_events(&mut events)?;

    Ok(Cfg {
        events,
        probes,
        probes_to_components,
    })
}

fn add_internal_events(events: &mut HashMap<(Uuid, u32), EventMeta>) -> Result<(), ExportError> {
    let nil_uuid = Uuid::nil();
    for ie in Events::internal_events() {
        let ev = EventMeta {
            component_id: nil_uuid,
            id: ie.id.0,
            name: ie.name,
            type_hint: if ie.type_hint.is_empty() {
                None
            } else {
                Some(ie.type_hint)
            },
            tags: ie.tags,
            description: ie.description,
            file: ie.file,
            line: str::parse::<u32>(&ie.line).map_err(|e| {
                ExportError(format!(
                    "encountered a bad internal event, unable to parse line number: {}",
                    e
                ))
            })?,
        };
        events.insert((nil_uuid, ie.id.0), ev.clone());
    }

    Ok(())
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
    use std::{fs, fs::File, io::Write};

    use tempfile::tempdir;
    use uuid::Uuid;

    use crate::graph::{EventMeta, ProbeMeta};

    const COMP_ONE_CONTENT: &'static str = r#"
name = "one"
id = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca1"
"#;
    const COMP_TWO_CONTENT: &'static str = r#"
name = "two"
id = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca2"
"#;
    const PROBE_ONE_CONTENT: &'static str = "
component_id,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,PROBE_ONE,probe one,example,examples/event-recording.rs,26";
    const PROBE_TWO_CONTENT: &'static str = "
component_id,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,PROBE_TWO,probe two,example,examples/event-recording.rs,26";

    const EVENT_ONE_CONTENT: &'static str = "
component_id,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,TEST_ONE,test event one,,,,26
";
    const EVENT_TWO_CONTENT: &'static str = "
component_id,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,TEST_TWO,test event two,,,,36
";

    #[test]
    fn comp_assembly() {
        let mut tmp_one = tempdir().unwrap().into_path();
        let mut tmp_two = tempdir().unwrap().into_path();

        {
            tmp_one.push("Component.toml");
            let mut comp_one = File::create(&tmp_one).unwrap();
            write!(comp_one, "{}", COMP_ONE_CONTENT).unwrap();
            tmp_one.pop();
            tmp_one.push("probes.csv");
            let mut probe_one = File::create(&tmp_one).unwrap();
            write!(probe_one, "{}", PROBE_ONE_CONTENT).unwrap();
            tmp_one.pop();
            tmp_one.push("events.csv");
            let mut event_one = File::create(&tmp_one).unwrap();
            write!(event_one, "{}", EVENT_ONE_CONTENT).unwrap();

            tmp_two.push("Component.toml");
            let mut comp_two = File::create(&tmp_two).unwrap();
            write!(comp_two, "{}", COMP_TWO_CONTENT).unwrap();
            tmp_two.pop();
            tmp_two.push("probes.csv");
            let mut probe_two = File::create(&tmp_two).unwrap();
            write!(probe_two, "{}", PROBE_TWO_CONTENT).unwrap();
            tmp_two.pop();
            tmp_two.push("events.csv");
            let mut event_two = File::create(&tmp_two).unwrap();
            write!(event_two, "{}", EVENT_TWO_CONTENT).unwrap();

            let expected_probes = vec![
                (
                    1,
                    ProbeMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1")
                            .unwrap(),
                        id: 1,
                        name: "PROBE_ONE".to_string(),
                        description: "probe one".to_string(),
                        file: "examples/event-recording.rs".to_string(),
                        line: 26,
                    },
                ),
                (
                    2,
                    ProbeMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2")
                            .unwrap(),
                        id: 2,
                        name: "PROBE_TWO".to_string(),
                        description: "probe two".to_string(),
                        file: "examples/event-recording.rs".to_string(),
                        line: 26,
                    },
                ),
            ]
            .into_iter()
            .collect();

            let mut expected_events = vec![
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca1").unwrap(),
                        1,
                    ),
                    EventMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1")
                            .unwrap(),
                        id: 1,
                        name: "TEST_ONE".to_string(),
                        description: "test event one".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: 26,
                    },
                ),
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca2").unwrap(),
                        2,
                    ),
                    EventMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2")
                            .unwrap(),
                        id: 2,
                        name: "TEST_TWO".to_string(),
                        description: "test event two".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: 36,
                    },
                ),
            ]
            .into_iter()
            .collect();

            super::add_internal_events(&mut expected_events).unwrap();

            tmp_one.pop();
            tmp_two.pop();
            let cfg =
                super::assemble_components(&mut vec![tmp_one.clone(), tmp_two.clone()]).unwrap();

            assert_eq!(&cfg.probes, &expected_probes);
            assert_eq!(&cfg.events, &expected_events);
        }

        fs::remove_dir_all(&tmp_one).unwrap();
        fs::remove_dir_all(&tmp_two).unwrap();
    }
}
