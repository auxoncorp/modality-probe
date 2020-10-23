//! Export a textual representation of a causal graph using the
//! collected columnar form as input.

use std::{fs::File, path::PathBuf, str::FromStr};

use structopt::StructOpt;

use modality_probe_collector_common::json;

use crate::{give_up, hopefully, meta};

pub mod graph;
mod templates;

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

#[derive(Debug, PartialEq, StructOpt)]
pub enum GraphType {
    Cyclic,
    Acyclic,
}

impl FromStr for GraphType {
    type Err = Box<dyn std::error::Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "cyclic" => Ok(GraphType::Cyclic),
            "acyclic" => Ok(GraphType::Acyclic),
            _ => give_up!(format!("{} is not a valid graph type", s)),
        }
    }
}

pub fn run(mut exp: Export) -> Result<(), Box<dyn std::error::Error>> {
    let cfg = meta::assemble_components(&mut exp.components)?;
    let mut log_file = hopefully!(
        File::open(&exp.report),
        format!("Failed to open the report file at {}", exp.report.display(),)
    )?;

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
