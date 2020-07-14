//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{collections::HashMap, path::PathBuf, str::FromStr};

use structopt::StructOpt;

use crate::{
    component::Component,
    graph::{self, digraph::Digraph, meta::*, Cfg},
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
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "cyclic" => Ok(GraphType::Cyclic),
            "acyclic" => Ok(GraphType::Acyclic),
            _ => Err(format!("{} is not a valid graph type", s)),
        }
    }
}

pub fn run(mut exp: Export) -> Result<(), String> {
    let (cfg, probes_by_name, events_by_name) = assemble_components(&mut exp.components)?;
    let mut lrdr = csv::Reader::from_path(&exp.report).map_err(|e| {
        format!(
            "failed to open the report file at {}: {}",
            exp.report.display(),
            e
        )
    })?;

    match (exp.graph_type, exp.interactions_only) {
        (GraphType::Cyclic, false) => {
            let mut graph = Digraph::new();
            graph::overlay(&cfg, &mut graph, lrdr.deserialize())
                .map_err(|e| format!("building the graph failed: {}", e))?;
            println!("{}", graph.to_dot(
                |n, _| Ok((*n).to_string()),
                |n, w| {
                    let event = events_by_name.get(*n).ok_or_else(|| format!("couldn't find an event to match the name {}", n))?;
                    Ok(match event.line {
                        Some(line) => format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" line = {} tags = \"{}\" weight = {} raw_event_id = {}",
                            event.name,
                            event.description,
                            event.file,
                            line,
                            event.tags,
                            w,
                            event.id
                        ),
                        None => format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" tags = \"{}\" weight = {} raw_event_id = {}",
                            event.name,
                            event.description,
                            event.file,
                            event.tags,
                            w,
                            event.id
                        )})
                },
                |_from, _to, weight| {
                    Ok(format!(
                        "weight = {}",
                        weight
                    ))
                },
            ).map_err(|e| format!("generating the graph output failed: {}", e))?);
        }
        (GraphType::Cyclic, true) => {
            let mut graph = Digraph::new();
            graph::topo(&cfg, &mut graph, lrdr.deserialize())
                .map_err(|e| format!("building the graph failed: {}", e))?;
            println!(
                "{}",
                graph.to_dot(
                    |n, _| Ok((*n).to_string()),
                    |n, w| {
                        let probe = probes_by_name.get(*n).ok_or_else(|| format!("couldn't find a probe to match the name {}", n))?;
                        Ok(format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" line = {} raw_probe_id = {} weight = {}",
                            n, probe.description, probe.file, probe.line, probe.id, w
                        ))
                    },
                    |_from, _to, weight| Ok(format!("weight = {}", weight))

            ).map_err(|e| format!("generating the graph output failed: {}", e))?);
        }
        (GraphType::Acyclic, false) => {
            let mut graph = Digraph::new();
            graph::complete(&cfg, &mut graph, lrdr.deserialize())
                .map_err(|e| format!("building the graph failed: {}", e))?;
            println!(
                "{}",
                graph.to_dot(
                    |n, _| Ok(format!("{}_{}_{}", n.name(), n.clock(), n.clock_offset())),
                    |n, _| {
                        let event = events_by_name.get(n.name()).ok_or_else(|| format!("couldn't find an event to match the name {}", n.name()))?;
                        let probe = probes_by_name.get(n.name()).ok_or_else(|| format!("couldn't find a probe to match the name {}", n.name()))?;
                        Ok(if let Some(th) = &event.type_hint {
                            match (event.line, n.parsed_payload(th)) {
                                (Some(line), Some(p)) => format!(
                                    "label = \"{}\" payload = {} type_hint = \"{}\" description = \"{}\" file = \"{}\" line = {} probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {} raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    p,
                                    th,
                                    event.description,
                                    event.file,
                                    line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                ),
                                (Some(line), None) => format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" line = {} probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {}, raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    event.description,
                                    event.file,
                                    line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                ),
                                (None, Some(p)) => format!(
                                    "label = \"{}\" payload = {} type_hint = \"{}\" description = \"{}\" file = \"{}\" probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {} raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    p,
                                    th,
                                    event.description,
                                    event.file,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                ),
                                (None, None) => format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {}, raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    event.description,
                                    event.file,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                ),
                            }
                        } else {
                            match event.line {
                                Some(line) => format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" line = {} probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {}, raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    event.description,
                                    event.file,
                                    line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                ),
                                None => format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" probe = \"{}\" tags = \"{}\" probe_epoch = {} epoch_offset = {}, raw_event_id = {} raw_probe_id = {}",
                                    event.name,
                                    event.description,
                                    event.file,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event.id,
                                    probe.id
                                )}
                        })
                    },
                    |_from, _to, _weight| Ok(String::new()),
            ).map_err(|e| format!("generating the graph output failed: {}", e))?);
        }
        (GraphType::Acyclic, true) => {
            let mut graph = Digraph::new();
            graph::segments(&cfg, &mut graph, lrdr.deserialize())
                .map_err(|e| format!("building the graph failed: {}", e))?;
            println!(
                "{}",
                graph.to_dot(
                    |n, _| Ok(format!("{}_{}", n.name, n.clock)),
                    |n, w| {
                        let probe = probes_by_name.get(n.name).ok_or_else(|| format!("couldn't find a probe to match the name {}", n.name))?;
                        Ok(format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" line = {} probe_epoch = {} raw_probe_id = {} weight = {}",
                            probe.name, probe.description, probe.file, probe.line, n.clock, probe.id, w
                        ))
                    },
                    |_from, _to, weight| Ok(format!("weight = {}", weight)),
            ).map_err(|e| format!("generating the graph output failed: {}", e))?);
        }
    };
    Ok(())
}

type Comps = (Cfg, HashMap<String, ProbeMeta>, HashMap<String, EventMeta>);

fn assemble_components(comp_dirs: &mut Vec<PathBuf>) -> Result<Comps, String> {
    let mut probes = HashMap::new();
    let mut probes_by_name = HashMap::new();
    let mut probes_to_components = HashMap::new();
    let mut events = HashMap::new();
    let mut events_by_name = HashMap::new();

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
        let mut pr_rdr = csv::Reader::from_path(pf.clone())
            .map_err(|e| format!("failed to open the probes file at {}: {}", pf.display(), e))?;
        for res in pr_rdr.deserialize() {
            let p: ProbeMeta =
                res.map_err(|e| format!("failed to deserialize a probe row: {}", e))?;
            pf.pop();
            pf.push("Component.toml");
            let comp = Component::from_toml(&pf);
            probes.insert(p.id, p.clone());
            probes_by_name.insert(p.name.clone(), p.clone());
            probes_to_components.insert(p.id, comp.uuid.0);
        }
    }
    for ef in event_files.iter_mut() {
        let mut ev_rdr = csv::Reader::from_path(ef.clone())
            .map_err(|e| format!("failed to open the events file at {}: {}", ef.display(), e))?;
        for res in ev_rdr.deserialize() {
            let e: EventMeta =
                res.map_err(|e| format!("failed to deserialize a event row: {}", e))?;
            ef.pop();
            ef.push("Component.toml");
            let comp = Component::from_toml(&ef);
            events.insert((comp.uuid.0, e.id), e.clone());
            events_by_name.insert(e.name.clone(), e);
        }
    }
    Ok((
        Cfg {
            events,
            probes,
            probes_to_components,
        },
        probes_by_name,
        events_by_name,
    ))
}

#[cfg(test)]
mod test {
    use std::{fs, fs::File, io::Write};

    use tempfile::tempdir;
    use uuid::Uuid;

    use crate::export::graph::meta::*;

    const COMP_ONE_CONTENT: &'static str = r#"
name = "one"
uuid = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca1"
"#;
    const COMP_TWO_CONTENT: &'static str = r#"
name = "two"
uuid = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca2"
"#;
    const PROBE_ONE_CONTENT: &'static str = "
uuid,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,PROBE_ONE,probe one,example,examples/event-recording.rs,26";
    const PROBE_TWO_CONTENT: &'static str = "
uuid,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,PROBE_TWO,probe two,example,examples/event-recording.rs,26";

    const EVENT_ONE_CONTENT: &'static str = "
uuid,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,TEST_ONE,test event one,,,,
";
    const EVENT_TWO_CONTENT: &'static str = "
uuid,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,TEST_TWO,test event two,,,,
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
                        uuid: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1").unwrap(),
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
                        uuid: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2").unwrap(),
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

            let expected_events = vec![
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca1").unwrap(),
                        1,
                    ),
                    EventMeta {
                        uuid: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1").unwrap(),
                        id: 1,
                        name: "TEST_ONE".to_string(),
                        description: "test event one".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: None,
                    },
                ),
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca2").unwrap(),
                        2,
                    ),
                    EventMeta {
                        uuid: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2").unwrap(),
                        id: 2,
                        name: "TEST_TWO".to_string(),
                        description: "test event two".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: None,
                    },
                ),
            ]
            .into_iter()
            .collect();

            tmp_one.pop();
            tmp_two.pop();
            let (cfg, _, _) =
                super::assemble_components(&mut vec![tmp_one.clone(), tmp_two.clone()]).unwrap();

            assert_eq!(&cfg.probes, &expected_probes);
            assert_eq!(&cfg.events, &expected_events);
        }

        fs::remove_dir_all(&tmp_one).unwrap();
        fs::remove_dir_all(&tmp_two).unwrap();
    }
}
