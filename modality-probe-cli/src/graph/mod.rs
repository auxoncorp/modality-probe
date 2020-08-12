//! `modality-probe-graph` is a library that builds different types of node
//! and edge lists from a columnar, unordered collection of log
//! reports like the one that modality-probe-udp-collector creates.
use err_derive::Error;

pub mod digraph;
pub mod graph_event;
pub mod meta;

/// Errors returned by the graph building operations or the exporters.
#[derive(Debug, Error)]
pub enum Error {
    /// Encountered an error when using the writer when exporting a
    /// graph in a textual format.
    #[error(display = "Formatting graph failed: {}", _0)]
    Io(String),
    /// The graph builders iterate over a `Result` to leave room for
    /// deserialization; if a builder encounters a `Err`, this error
    /// is returned with that error's `display` implementaion inside.
    #[error(display = "An item in the log iterator was an error variant: {}", _0)]
    ItemError(String),
    /// Encountered an unexpected inconsistency in the graph data.
    #[error(display = "Encountered an inconsistency in the graph data: {}", _0)]
    InconsistentData(&'static str),
}
