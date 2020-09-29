//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{collections::HashMap, fmt, fs::File, path::PathBuf, str::FromStr};

use err_derive::Error;
use structopt::StructOpt;
use uuid::Uuid;

use modality_probe::ProbeId;
use modality_probe_collector_common::{json, Error as CollectorError};

use crate::{component::Component, events::Events};

mod templates;

mod graph;
use graph::{EventMeta, ProbeMeta};

/// Export a textual representation of a causal graph using the
/// collected trace file as input.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Export {
    /// Generate the graph showing only the causal relationships,
    /// eliding the events in between.
    #[structopt(long)]
    pub interactions_only: bool,
    /// Include probe-generated events in the output.
    #[structopt(long)]
    pub include_internal_events: bool,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub components: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
    /// The type of graph to output.
    ///
    /// This can be either `cyclic` or `acyclic`. A cyclic graph is
    /// one which shows the possible paths from either an event or a
    /// probe. An acyclic graph shows the causal history of either all
    /// events or the interactions between probes in the system.
    #[structopt(required = true)]
    pub graph_type: GraphType,
}

/// Inspect the event log from the perspective of a single probe.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Log {
    /// The probe to target.
    #[structopt(short, long)]
    pub probe: String,
    /// The path to a component directory. To include multiple
    /// components, provide this switch multiple times.
    #[structopt(short, long, required = true)]
    pub components: Vec<PathBuf>,
    /// The path to the collected trace.
    #[structopt(short, long, required = true)]
    pub report: PathBuf,
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

impl From<CollectorError> for ExportError {
    fn from(e: CollectorError) -> Self {
        ExportError(format!("failed to read log file: {}", e))
    }
}

pub fn log(mut l: Log) -> Result<(), ExportError> {
    let cfg = assemble_components(&mut l.components)?;
    let mut log_file = File::open(&l.report).map_err(|e| {
        ExportError(format!(
            "failed to open the report file at {}: {}",
            l.report.display(),
            e
        ))
    })?;

    let graph = graph::log_to_graph(
        json::read_log_entries(&mut log_file)?
            .into_iter()
            .peekable(),
    )?;

    let probe = match cfg.probes.iter().find(|(_, v)| v.name == l.probe) {
        Some((_, pm)) => pm,
        None => {
            let pid = l
                .probe
                .parse::<u32>()
                .map_err(|_| ExportError(format!("probe {} could not be found", l.probe)))?;
            cfg.probes
                .get(&pid)
                .ok_or_else(|| ExportError(format!("probe {} could not be found", l.probe)))?
        }
    };
    let log = graph.graph.probe_log(ProbeId::new(probe.id).ok_or_else(|| {
        ExportError(format!(
            "encountered the invalid probe id {} when looking up probe {}",
            probe.id, l.probe
        ))
    })?);
    for l in log {
        let emeta = graph::get_event_meta(&cfg, &l.probe_id, &l.id)?;
        let probe_name = cfg
            .probes
            .get(&l.probe_id.get_raw())
            .map(|p| p.name.clone())
            .unwrap_or(format!("UNKNOWN_PROBE_{}", l.probe_id.get_raw()));
        println!(
            "{} probe={} description={}{}{}tags={}{}",
            emeta.name,
            probe_name,
            emeta.description,
            if !emeta.file.is_empty() {
                format!(" file={} ", emeta.file)
            } else {
                "".to_string()
            },
            if !emeta.line.is_empty() {
                format!(" line={} ", emeta.line)
            } else {
                "".to_string()
            },
            emeta.tags,
            match l.payload {
                Some(p) => format!(
                    " payload={}",
                    graph::parsed_payload(&emeta.type_hint.as_ref().unwrap(), p)?
                ),
                None => "".to_string(),
            }
        );
    }
    Ok(())
}

pub fn run(mut exp: Export) -> Result<(), ExportError> {
    let cfg = assemble_components(&mut exp.components)?;
    let mut log_file = File::open(&exp.report).map_err(|e| {
        ExportError(format!(
            "failed to open the report file at {}: {}",
            exp.report.display(),
            e
        ))
    })?;

    let graph = graph::log_to_graph(
        json::read_log_entries(&mut log_file)?
            .into_iter()
            .peekable(),
    )?;

    match (exp.graph_type, exp.interactions_only) {
        (GraphType::Acyclic, false) => println!(
            "{}",
            graph.graph.as_complete(exp.include_internal_events).dot(
                &cfg,
                "complete",
                templates::COMPLETE
            )?
        ),
        (GraphType::Acyclic, true) => println!(
            "{}",
            graph
                .graph
                .as_interactions()
                .dot(&cfg, "interactions", templates::INTERACTIONS)?
        ),
        (GraphType::Cyclic, false) => println!(
            "{}",
            graph.graph.as_states(exp.include_internal_events).dot(
                &cfg,
                "states",
                templates::STATES
            )?
        ),
        (GraphType::Cyclic, true) => println!(
            "{}",
            graph
                .graph
                .as_topology()
                .dot(&cfg, "topo", templates::TOPO)?
        ),
    }

    Ok(())
}

pub struct Cfg {
    pub probes: HashMap<u32, ProbeMeta>,
    pub events: HashMap<(Uuid, u32), EventMeta>,
    pub probes_to_components: HashMap<u32, Uuid>,
    pub component_names: HashMap<String, String>,
}

fn assemble_components(comp_dirs: &mut Vec<PathBuf>) -> Result<Cfg, ExportError> {
    let mut probes = HashMap::new();
    let mut probes_to_components = HashMap::new();
    let mut events = HashMap::new();
    let mut component_names = HashMap::new();

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
            component_names.insert(comp.id.0.to_string(), comp.name);
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
        component_names,
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
            line: ie.line,
        };
        events.insert((nil_uuid, ie.id.0), ev.clone());
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use std::{fs, fs::File, io::Write};

    use tempfile::tempdir;
    use uuid::Uuid;

    use super::graph::{EventMeta, ProbeMeta};

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
                        line: "26".to_string(),
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
                        line: "26".to_string(),
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
                        line: "26".to_string(),
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
                        line: "36".to_string(),
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
