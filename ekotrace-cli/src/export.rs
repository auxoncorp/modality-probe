use std::{collections::HashMap, path::PathBuf, str::FromStr};

use structopt::StructOpt;

use ekotrace_graph::{digraph::Digraph, meta::*, Cfg};

#[derive(Debug, StructOpt)]
pub struct Export {
    #[structopt(long)]
    segments_only: bool,
    #[structopt(long)]
    tracers: PathBuf,
    #[structopt(long)]
    events: PathBuf,
    #[structopt(long)]
    report: PathBuf,
    graph_type: GraphType,
}

#[derive(Debug, StructOpt)]
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

pub fn run(exp: Export) {
    let mut tr_rdr = csv::Reader::from_path(&exp.tracers).unwrap();
    let mut tracers = HashMap::new();
    let mut tracers_by_name = HashMap::new();
    for res in tr_rdr.deserialize() {
        let e: TracerMeta = res.unwrap();
        tracers.insert(e.id, e.clone());
        tracers_by_name.insert(e.name.clone(), e);
    }

    let mut ev_rdr = csv::Reader::from_path(&exp.events).unwrap();
    let mut events = HashMap::new();
    let mut events_by_name = HashMap::new();
    for res in ev_rdr.deserialize() {
        let e: EventMeta = res.unwrap();
        events.insert(e.id, e.clone());
        events_by_name.insert(e.name.clone(), e);
    }

    let mut lrdr = csv::Reader::from_path(&exp.report).unwrap();

    let cfg = Cfg {
        tracers: tracers.clone(),
        events: events.clone(),
    };

    match (exp.graph_type, exp.segments_only) {
        (GraphType::Cyclic, false) => {
            let mut graph = Digraph::new();
            ekotrace_graph::overlay(&cfg, &mut graph, lrdr.deserialize()).unwrap();
            println!("{}", graph.to_dot(
                |n, _| n.to_string(),
                |n, w| {
                    let event = events_by_name.get(*n).unwrap();
                    let event_id = events.iter().filter(|(_, v)| v.name == *n).map(|(k, _)| k).next().unwrap();
                    format!(
                        "label = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" tags = \"{}\" occurrence = \"{}\" raw_event_id = \"{}\"",
                        event.name,
                        event.description,
                        event.file,
                        event.line,
                        event.tags,
                        w,
                        event_id
                    )
                },
                |_from, _to, weight| {
                    format!(
                        "occurrence = \"{}\"",
                        weight
                    )
                },
            ));
        }
        (GraphType::Cyclic, true) => {
            let mut graph = Digraph::new();
            ekotrace_graph::topo(&cfg, &mut graph, lrdr.deserialize()).unwrap();
            println!(
                "{}",
                graph.to_dot(
                    |n, _| n.to_string(),
                    |n, _| {
                        let tracer = tracers_by_name.get(*n).unwrap();
                        let tracer_id = tracers.iter().filter(|(_, v)| v.name == *n).map(|(k, _)| k).next().unwrap();
                        format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" raw_location_id = \"{}\"",
                            n, tracer.description, tracer.file, tracer.line, tracer_id
                        )
                    },
                    |_from, _to, weight| format!("occurrence = \"{}\"", weight)
                )
            );
        }
        (GraphType::Acyclic, false) => {
            let mut graph = Digraph::new();
            ekotrace_graph::complete(&cfg, &mut graph, lrdr.deserialize()).unwrap();
            println!(
                "{}",
                graph.to_dot(
                    |n, _| format!("{}_{}_{}", n.name(), n.clock(), n.clock_offset()),
                    |n, _| {
                        let event = events_by_name.get(n.name()).unwrap();
                        let event_id = events.iter().filter(|(_, v)| v.name == n.name()).map(|(k, _)| k).next().unwrap();
                        let tracer_id = tracers.iter().filter(|(_, v)| v.name == n.name()).map(|(k, _)| k).next().unwrap();
                        if let Some(th) = &event.type_hint {
                            match n.parsed_payload(th) {
                                Some(p) => format!(
                                    "label = \"{}\" payload = \"{}\" type_hint = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" location = \"{}\" tags = \"{}\" clock = \"{}\" clock_offset = \"{}\" raw_event_id = \"{}\" raw_location_id = \"{}\"",
                                    event.name,
                                    p,
                                    th,
                                    event.description,
                                    event.file,
                                    event.line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event_id,
                                    tracer_id
                                ),
                                None => format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" location = \"{}\" tags = \"{}\" clock = \"{}\" clock_offset = \"{}\", raw_event_id = \"{}\" raw_location_id = \"{}\"",
                                    event.name,
                                    event.description,
                                    event.file,
                                    event.line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event_id,
                                    tracer_id
                                ),
                            }
                        } else {
                            format!(
                                    "label = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" location = \"{}\" tags = \"{}\" clock = \"{}\" clock_offset = \"{}\", raw_event_id = \"{}\" raw_location_id = \"{}\"",
                                    event.name,
                                    event.description,
                                    event.file,
                                    event.line,
                                    n.location(),
                                    event.tags,
                                    n.clock(),
                                    n.clock_offset(),
                                    event_id,
                                    tracer_id
                            )
                        }
                    },
                    |_from, _to, _weight| String::new(),
                )
            );
        }
        (GraphType::Acyclic, true) => {
            let mut graph = Digraph::new();
            ekotrace_graph::segments(&cfg, &mut graph, lrdr.deserialize()).unwrap();
            println!(
                "{}",
                graph.to_dot(
                    |n, _| format!("{}_{}", n.name, n.clock),
                    |n, _| {
                        let tracer = tracers_by_name.get(n.name).unwrap();
                        let tracer_id = tracers.iter().filter(|(_, v)| v.name == n.name).map(|(k, _)| k).next().unwrap();
                        format!(
                            "label = \"{}\" description = \"{}\" file = \"{}\" line = \"{}\" clock = \"{}\" raw_location_id = \"{}\"",
                            tracer.name, tracer.description, tracer.file, tracer.line, n.clock, tracer_id,
                        )
                    },
                    |_from, _to, _weight| String::new(),
                )
            );
        }
    }
}
