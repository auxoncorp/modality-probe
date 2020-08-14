//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{collections::HashMap, fmt, fmt::Write, path::PathBuf, str::FromStr};

use err_derive::Error;
use structopt::StructOpt;
use uuid::Uuid;

use crate::{component::Component, events::Events};

mod graph;
use graph::{EventMeta, ProbeMeta};

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

    let graph = graph::log_to_graph(lrdr.deserialize().peekable())?;

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
