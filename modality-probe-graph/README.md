# modality-probe-graph

This crate provides types and implementations for building a graph out
of a probe's report.

Example usage:

```rust
fn log_to_graph<I, E>(
    log: Peekable<I>,
) -> Result<EventDigraph<NodeAndEdgeLists<GraphEvent, ()>>, ExportError>
where
    I: Iterator<Item = Result<LogFileRow, E>>,
    E: std::error::Error,
    for<'a> &'a E: Into<ReadError>,
{
    let mut graph = EventDigraph::new(NodeAndEdgeLists {
        nodes: HashMap::new(),
        edges: HashMap::new(),
    });
    let report_iter = ReportIter::new(log);
    for report in report_iter {
        graph
            .add_report(&report.map_err(|e| {
                ExportError(format!(
                    "encountered an error deserializing the report: {}",
                    e
                ))
            })?)
            .map_err(|e| {
                ExportError(format!(
                    "encountered an error reconstructing the graph: {}",
                    e
                ))
            })?;
    }
    Ok(graph)
}
```
