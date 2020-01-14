use itertools::Itertools;
use std::path::PathBuf;
use std::str::FromStr;
use structopt::StructOpt;
use itertools::Itertools;

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
        session_id: u32
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

struct GraphNode {
    tracer_id: model::TracerId,
    segment_id: model::SegmentId,
    event_count: usize,
}

fn segment_graph(event_log_csv_file: PathBuf, session_id: model::SessionId) {
    // Read the events CSV file
    let mut csv_file = std::fs::File::open(event_log_csv_file).expect("Open CSV file");
    let log_entries = lib::read_csv_log_entries(&mut csv_file).expect("Read events CSV file");

    // let mut seg_graph = Graph::new();

    let nodes: Vec<_> = log_entries
        .iter()
        .filter(|e| e.session_id == session_id)
        .group_by(|e| (e.tracer_id, e.segment_id))
        .into_iter()
        .map(|((tracer_id, segment_id), events)| GraphNode {
            tracer_id,
            segment_id,
            event_count: events.count(),
        })
        .collect();

    let nodes_by_tracer = nodes.iter().map(|n| (n.tracer_id, n)).into_group_map();

    println!("digraph G {{");
    println!("  rankdir=BT;");
    for (tracer_id, nodes) in nodes_by_tracer.iter() {
        println!("  subgraph cluster_tracer_{} {{", tracer_id.0);
        println!("    label = \"tracer {}\";", tracer_id.0);
        for node in nodes.iter() {
            println!(
                "    segment_{} [label=\"Segment {}\\n({} events)\"]",
                node.segment_id.0, node.segment_id.0, node.event_count
            );
        }

        println!("  }}");
    }

    for l in lib::synthesize_cross_segment_links(log_entries.iter(), session_id).iter() {
        println!("  segment_{} -> segment_{};", l.after.0, l.before.0);
    }

    println!("}}");
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
        Opt::SegmentGraph { event_log_csv_file, session_id } => segment_graph(event_log_csv_file, session_id.into()),
        Opt::QueryCausedBy {
            event_log_csv_file,
            event_a,
            event_b,
        } => query_caused_by(event_log_csv_file, event_a, event_b),
    }

    // Generate indexes
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
