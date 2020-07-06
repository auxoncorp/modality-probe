//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{collections::HashMap, path::PathBuf, str::FromStr};

use structopt::StructOpt;

use crate::graph::{self, digraph::Digraph, meta::*, Cfg};

/// Export a textual representation of a causal graph using the
/// collected coumnar form as input.
#[derive(Debug, PartialEq, StructOpt)]
pub struct Export {
    /// Generate the graph showing only the causal relationships,
    /// eliding the events inbetween.
    #[structopt(long)]
    pub interactions_only: bool,
    /// The path the probes.csv for a component.
    #[structopt(long)]
    pub probes: PathBuf,
    /// The path the events.csv for a component.
    #[structopt(long)]
    pub events: PathBuf,
    /// The path to the file containing the collected traces.
    #[structopt(long)]
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

pub fn run(exp: Export) -> Result<(), String> {
    let mut tr_rdr = csv::Reader::from_path(&exp.probes).map_err(|e| {
        format!(
            "failed to open the probes file at {}: {}",
            exp.probes.display(),
            e
        )
    })?;
    let mut probes = HashMap::new();
    let mut probes_by_name = HashMap::new();
    for res in tr_rdr.deserialize() {
        let e: ProbeMeta = res.map_err(|e| format!("failed to deserialize a probe row: {}", e))?;
        probes.insert(e.id, e.clone());
        probes_by_name.insert(e.name.clone(), e);
    }

    let mut ev_rdr = csv::Reader::from_path(&exp.events).map_err(|e| {
        format!(
            "failed to open the events file at {}: {}",
            exp.events.display(),
            e
        )
    })?;
    let mut events = HashMap::new();
    let mut events_by_name = HashMap::new();
    for res in ev_rdr.deserialize() {
        let e: EventMeta = res.map_err(|e| format!("failed to deserialize an event row: {}", e))?;
        events.insert(e.id, e.clone());
        events_by_name.insert(e.name.clone(), e);
    }

    let mut lrdr = csv::Reader::from_path(&exp.report).map_err(|e| {
        format!(
            "failed to open the report file at {}: {}",
            exp.report.display(),
            e
        )
    })?;

    let cfg = Cfg { probes, events };

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
