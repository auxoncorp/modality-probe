use itertools::Itertools;
use petgraph::graph::Graph;
use petgraph::visit::IntoNodeReferences;
use std::path::PathBuf;
use std::str::FromStr;
use structopt::StructOpt;

use ekotrace_analysis as lib;
use ekotrace_analysis::model;

#[derive(Debug, StructOpt)]
#[structopt(name = "truce-analysis", about = "Analyze 'truce' event logs")]
enum Opt {
    SessionSummary {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,
    },

    /// Produce a graphviz (.dot) formatted graph of log segments and direct
    /// causal relationships. The .dot source is printed to standard out.
    SegmentGraph {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,

        /// The session to graph
        session_id: u32,
    },

    /// See if event A is caused by (is a causal descendant of) event B. Events
    /// are identified by "<session id>.<segment id>.<segment index>".
    QueryCausedBy {
        /// Event log csv file
        #[structopt(parse(from_os_str))]
        event_log_csv_file: PathBuf,

        event_a: EventCoordinates,
        event_b: EventCoordinates,
    },
}

#[derive(Debug)]
struct EventCoordinates {
    session_id: model::SessionId,
    segment_id: model::SegmentId,
    segment_index: u32,
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
enum EventParseError {
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
        let mut it = s.split(".");
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

fn session_summary(event_log_csv_file: PathBuf) {
    // Read the events CSV file
    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    let log_entries = lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file");

    println!("SessionId\tEvent Count");
    for (session_id, session_entries) in &log_entries.iter().group_by(|e| e.session_id) {
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

/// Print a graph in Dot format, but with clustered nodes.
fn print_clustered_graph<N: ClusteredNodeFmt, E>(g: &Graph<N, E>) {
    let node_indicies_by_cluster = g
        .node_references()
        .into_iter()
        .map(|(node_index, node)| ((node.cluster_id(), node.cluster_label()), node_index))
        .into_group_map();

    println!("digraph G {{");
    println!("  rankdir=BT;");
    for ((cluster_id, cluster_label), node_indicies) in node_indicies_by_cluster.iter() {
        println!("  subgraph cluster_{} {{", cluster_id);
        println!("    label = \"{}\";", cluster_label);
        for node_index in node_indicies.into_iter() {
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

    let sg = lib::build_segment_graph(&log_entries, session_id);
    print_clustered_graph(&sg);
}

fn query_caused_by(
    _event_log_csv_file: PathBuf,
    _event_a: EventCoordinates,
    _event_b: EventCoordinates,
) {
    unimplemented!()
}

fn main() {
    let opt = Opt::from_args();
    match opt {
        Opt::SessionSummary { event_log_csv_file } => session_summary(event_log_csv_file),
        Opt::SegmentGraph {
            event_log_csv_file,
            session_id,
        } => segment_graph(event_log_csv_file, session_id.into()),
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
