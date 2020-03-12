use itertools::Itertools;
use petgraph::graph::Graph;
use petgraph::visit::IntoNodeReferences;
use std::path::PathBuf;
use std::str::FromStr;

use util as lib;
use util::model;

#[derive(Debug)]
pub enum Opt {
    SessionSummary {
        event_log_csv_file: PathBuf,
    },

    SegmentGraph {
        event_log_csv_file: PathBuf,
        session_id: u32,
    },

    EventGraph {
        event_log_csv_file: PathBuf,
        session_id: u32,
    },

    QueryCausedBy {
        event_log_csv_file: PathBuf,
        event_a: EventCoordinates,
        event_b: EventCoordinates,
    },
}

#[derive(Debug)]
pub struct EventCoordinates {
    pub session_id: model::SessionId,
    pub segment_id: model::SegmentId,
    pub segment_index: u32,
}

impl std::string::ToString for EventCoordinates {
    fn to_string(&self) -> String {
        format!(
            "{}.{}.{}",
            self.session_id.0, self.segment_id.0, self.segment_index
        )
    }
}

#[derive(Debug)]
pub enum EventParseError {
    InvalidSessionId,
    InvalidSegmentId,
    InvalidSegmentIndex,
    MissingSessionId,
    MissingSegmentId,
    MissingSegmentIndex,
}

impl std::string::ToString for EventParseError {
    fn to_string(&self) -> String {
        match self {
            EventParseError::InvalidSessionId => "Invalid session id",
            EventParseError::InvalidSegmentId => "Invalid segment id",
            EventParseError::InvalidSegmentIndex => "Invalid segment index",
            EventParseError::MissingSessionId => "Missing session id",
            EventParseError::MissingSegmentId => "Missing segment id",
            EventParseError::MissingSegmentIndex => "Missing segment index",
        }
        .to_string()
    }
}

impl FromStr for EventCoordinates {
    type Err = EventParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut it = s.split('.');
        let session_id = it
            .next()
            .ok_or(EventParseError::MissingSessionId)?
            .parse::<u32>()
            .map_err(|_| EventParseError::InvalidSessionId)?
            .into();
        let segment_id = it
            .next()
            .ok_or(EventParseError::MissingSegmentId)?
            .parse::<u32>()
            .map_err(|_| EventParseError::InvalidSegmentId)?
            .into();
        let segment_index = it
            .next()
            .ok_or(EventParseError::MissingSegmentIndex)?
            .parse::<u32>()
            .map_err(|_| EventParseError::InvalidSegmentIndex)?;

        Ok(EventCoordinates {
            session_id,
            segment_id,
            segment_index,
        })
    }
}

fn load_event_log(event_log_csv_file: PathBuf) -> impl IntoIterator<Item = util::model::LogEntry> {
    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file")
}

fn session_summary(event_log_csv_file: PathBuf) {
    let log = load_event_log(event_log_csv_file);
    println!("SessionId\tEvent Count");
    for (session_id, session_entries) in &log.into_iter().group_by(|e| e.session_id) {
        println!("{}\t\t{}", session_id.0, session_entries.count());
    }
}

/// How to format graph nodes when using print_clustered_graph
trait ClusteredNodeFmt {
    fn node_label(&self) -> String;
    fn cluster_id(&self) -> u32;
    fn cluster_label(&self) -> String;
}

impl ClusteredNodeFmt for lib::SegmentGraphNode {
    fn node_label(&self) -> String {
        format!(
            "Segment {}\\n({} events)",
            self.segment_id.0, self.event_count
        )
    }

    fn cluster_id(&self) -> u32 {
        self.tracer_id.0
    }

    fn cluster_label(&self) -> String {
        format!("Tracer {}", self.tracer_id.0)
    }
}

impl ClusteredNodeFmt for model::LogEntry {
    fn node_label(&self) -> String {
        match self.data {
            model::LogEntryData::LogicalClock(tracer_id, count) => format!(
                "{}.{}.{}\\nLogical Clock: Tracer {} => {}",
                self.session_id.0, self.segment_id.0, self.segment_index, tracer_id.0, count
            ),
            model::LogEntryData::Event(eid) => format!(
                "{}.{}.{}\\nEvent: {}",
                self.session_id.0,
                self.segment_id.0,
                self.segment_index,
                eid.get_raw(),
            ),
            model::LogEntryData::EventWithMetadata(eid, meta) => format!(
                "{}.{}.{}\\nEvent: {}\\nMetadata: {}",
                self.session_id.0,
                self.segment_id.0,
                self.segment_index,
                eid.get_raw(),
                meta
            ),
        }
    }

    fn cluster_id(&self) -> u32 {
        self.tracer_id.0
    }

    fn cluster_label(&self) -> String {
        format!("Tracer {}", self.tracer_id.0)
    }
}

/// Print a graph in Dot format, but with clustered nodes.
fn print_clustered_graph<N: ClusteredNodeFmt, E>(g: &Graph<N, E>) {
    let node_indicies_by_cluster = g
        .node_references()
        .map(|(node_index, node)| ((node.cluster_id(), node.cluster_label()), node_index))
        .into_group_map();

    println!("digraph G {{");
    println!("  rankdir=BT;");
    for ((cluster_id, cluster_label), node_indicies) in node_indicies_by_cluster.iter() {
        println!("  subgraph cluster_{} {{", cluster_id);
        println!("    label = \"{}\";", cluster_label);
        for node_index in node_indicies.iter() {
            let id = node_index.index();
            println!(
                "    node_{} [label=\"{}\"]",
                id,
                g[*node_index].node_label()
            );
        }

        println!("  }}");
    }

    for e in g.raw_edges() {
        println!(
            "  node_{} -> node_{};",
            e.source().index(),
            e.target().index()
        );
    }

    println!("}}");
}

fn segment_graph(event_log_csv_file: PathBuf, session_id: model::SessionId) {
    // Read the events CSV file
    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    let log_entries = lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file");

    let sg = lib::build_segment_graph(&log_entries, session_id).expect("Analyze event causality");
    print_clustered_graph(&sg);
}

fn event_graph(event_log_csv_file: PathBuf, session_id: model::SessionId) {
    // let log_entries = load_event_log(event_log_csv_file);
    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    let log_entries = lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file");

    let eg = lib::build_log_entry_graph(&log_entries, session_id).expect("Analyze event causality");
    print_clustered_graph(&eg);
}

fn query_caused_by(
    event_log_csv_file: PathBuf,
    event_a: EventCoordinates,
    event_b: EventCoordinates,
) {
    assert!(event_a.session_id == event_b.session_id);

    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    let log_entries = lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file");

    let g = lib::build_segment_graph(&log_entries, event_a.session_id)
        .expect("Analyze event causality");
    let event_a_segment_index = g
        .node_indices()
        .find(|i| g[*i].segment_id == event_a.segment_id)
        .unwrap();

    let event_b_segment_index = g
        .node_indices()
        .find(|i| g[*i].segment_id == event_b.segment_id)
        .unwrap();

    let res = if event_a.segment_id == event_b.segment_id {
        event_a.segment_index < event_b.segment_index
    } else {
        petgraph::algo::has_path_connecting(&g, event_a_segment_index, event_b_segment_index, None)
    };

    if res {
        println!(
            "Node {} is in the history of node {}",
            event_a.to_string(),
            event_b.to_string()
        );
    } else {
        println!(
            "Node {} is NOT in the history of node {}",
            event_a.to_string(),
            event_b.to_string()
        );
    }
}

pub fn run(opt: Opt) {
    match opt {
        Opt::SessionSummary { event_log_csv_file } => session_summary(event_log_csv_file),
        Opt::SegmentGraph {
            event_log_csv_file,
            session_id,
        } => segment_graph(event_log_csv_file, session_id.into()),
        Opt::EventGraph {
            event_log_csv_file,
            session_id,
        } => event_graph(event_log_csv_file, session_id.into()),
        Opt::QueryCausedBy {
            event_log_csv_file,
            event_a,
            event_b,
        } => query_caused_by(event_log_csv_file, event_a, event_b),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_event_coords() {
        let c = EventCoordinates::from_str("1.2.3").unwrap();
        assert_eq!(c.session_id, 1.into());
        assert_eq!(c.segment_id, 2.into());
        assert_eq!(c.segment_index, 3);
    }
}
