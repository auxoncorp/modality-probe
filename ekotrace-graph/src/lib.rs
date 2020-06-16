//! `ekotrace-graph` is a library that builds different types of node
//! and edge lists from a columnar, unordered collection of log
//! reports like the one that ekotrace-udp-collector creates.
use std::{collections::HashMap, hash::Hash};

use err_derive::Error;

pub mod digraph;
pub mod graph_event;
pub mod meta;

use crate::{
    graph_event::{GraphEvent, GraphSegment},
    meta::{EventMeta, ReportEvent, TracerMeta},
};

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

/// The methods needed for building a basic graph. The builders that
/// _don't_ need weights use these, leaving it agnostic to the graph
/// type being used.
pub trait GraphBuilder<'a> {
    type Node: Eq + Hash + Clone + Copy;

    /// Add a node to the graph.
    fn add_node(&mut self, node: Self::Node);
    /// Add an edge to the graph, `from -> to`.
    fn add_edge(&mut self, from: Self::Node, to: Self::Node);
}

/// The methods needed for building a weighted graph. Like the
/// unweighted graph builders, this allows the builders to be agnostic
/// to the graph implementation.
pub trait GraphWithWeightsBuilder<'a> {
    type Node: Eq + Hash + Clone + Copy;
    type Weight: Clone + Copy;

    /// Add a weighted node to the graph.
    fn add_node(&mut self, node: Self::Node, weight: Self::Weight);
    /// Get a mutable reference to a node's weight if it exists. If it
    /// does not, insert it with the given weight, and then return a
    /// mutable reference.
    fn upsert_node(&mut self, node: Self::Node, weight: Self::Weight) -> &mut Self::Weight;
    /// Add a weighted edge to the graph.
    fn add_edge(&mut self, from: Self::Node, to: Self::Node, weight: Self::Weight);
    /// Get a mutable reference to a edge's weight if it exists. If it
    /// does not, insert it with the given weight, and then return a
    /// mutable reference.
    fn upsert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        weight: Self::Weight,
    ) -> &mut Self::Weight;
}

/// The metadata mapping event and tracer ids to their names and
/// descriptions, &c.
pub struct Cfg {
    pub tracers: HashMap<u32, TracerMeta>,
    pub events: HashMap<u32, EventMeta>,
}

/// `complete` builds a complete causal graph from the given data. The
/// cross-tracer relationship remains to be segment based, but arrows
/// are also drawn bewteen intra-segment events. This builder does not
/// require weights.
pub fn complete<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphBuilder<'a, Node = GraphEvent<'a>>,
    E: std::error::Error,
{
    // State needed for the fold.
    let mut prev_event = None;
    let mut last_seg_id = None;
    let mut last_ev_by_loc_clk: HashMap<(u32, u32), GraphEvent> = HashMap::new();
    let mut current_loc_clock = None;
    let mut first_event = true;
    let mut clock_set = Vec::new();
    let mut missing_segs = Vec::new();

    // Fold over the data set, for each segment collect the clocks and
    // add an edge from those neighbors. If we've not yet seen the
    // segment that that neighbor's clock points to, save it for
    // later. Once we've reached the end of the report, go back and
    // fill in the holes.
    for res in log {
        let event: ReportEvent = res.map_err(|e| Error::ItemError(format!("{}", e)))?;
        if event.lc_tracer_id.is_none() && event.lc_clock.is_none() {
            if let Some(meta_ev) = cfg.events.get(
                &event
                    .event_id
                    .ok_or_else(|| Error::InconsistentData("missing event id"))?,
            ) {
                let location = cfg
                    .tracers
                    .get(&event.tracer_id)
                    .ok_or_else(|| Error::InconsistentData("unknown tracer id"))?;
                let node = if let Some((_, clk)) = current_loc_clock {
                    match event.event_payload {
                        Some(payload) => GraphEvent::WithPayload {
                            payload,
                            location: &location.name,
                            name: &meta_ev.name,
                            clock: clk,
                            clock_offset: event.segment_index,
                        },
                        None => GraphEvent::Event {
                            location: &location.name,
                            name: &meta_ev.name,
                            clock: clk,
                            clock_offset: event.segment_index,
                        },
                    }
                } else {
                    return Err(Error::InconsistentData("no clock found for event"));
                };
                graph.add_node(node);
                if first_event {
                    for (loc, clk) in clock_set.iter() {
                        match last_ev_by_loc_clk.get(&(*loc, *clk)) {
                            Some(e) => {
                                graph.add_edge(*e, node);
                            }
                            None => missing_segs.push((*loc, *clk, node)),
                        }
                    }
                    first_event = false;
                    clock_set.clear();
                } else if let Some(pe) = prev_event {
                    graph.add_edge(pe, node);
                }

                prev_event = Some(node);
            }
        } else {
            let tracer = event
                .lc_tracer_id
                .ok_or_else(|| Error::InconsistentData("missing tracer id"))?;
            let clock = event
                .lc_clock
                .ok_or_else(|| Error::InconsistentData("missing logical clock"))?;
            if Some(event.segment_id) != last_seg_id && event.tracer_id == tracer {
                if let Some((loc, clock)) = current_loc_clock {
                    if let Some(prev) = prev_event {
                        last_ev_by_loc_clk.insert((loc, clock), prev);
                    }
                }
                current_loc_clock = Some((tracer, clock));
                last_seg_id = Some(event.segment_id);
                first_event = true;
            } else {
                clock_set.push((tracer, clock));
            }
        }
    }

    for (loc, clk, ev) in missing_segs {
        if let Some(e) = last_ev_by_loc_clk.get(&(loc, clk)) {
            graph.add_edge(*e, ev);
        }
    }

    Ok(())
}

/// `segments` builds a graph without events, it instead includes only
/// segments identified by their ids and their tracer locations.
pub fn segments<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphWithWeightsBuilder<'a, Node = GraphSegment<'a>, Weight = usize>,
    E: std::error::Error,
{
    let mut self_vertex = GraphSegment::default();
    let mut self_clocks = HashMap::new();

    // Accrue clocks for each segment and the draw edges for those
    // clocks. Otherwise, move along.
    for res in log {
        let event: ReportEvent = res.map_err(|e| Error::ItemError(format!("{}", e)))?;

        if event.lc_tracer_id.is_some() && event.lc_clock.is_some() {
            let tracer_name = match cfg.tracers.get(
                &event
                    .lc_tracer_id
                    .ok_or_else(|| Error::InconsistentData("missing tracer id"))?,
            ) {
                Some(s) => &s.name,
                None => "unknown_location",
            };

            let node = GraphSegment {
                name: tracer_name,
                clock: event
                    .lc_clock
                    .ok_or_else(|| Error::InconsistentData("missing logical clock"))?,
            };
            let weight = graph.upsert_node(node, 0);
            *weight += 1;
            if event.tracer_id
                == event
                    .lc_tracer_id
                    .ok_or_else(|| Error::InconsistentData("missing tracer id"))?
            {
                let this_clock = event
                    .lc_clock
                    .ok_or_else(|| Error::InconsistentData("missing logical clock"))?;
                let c = self_clocks.entry(tracer_name).or_insert_with(Vec::new);
                c.push(this_clock);
                c.sort();
                self_vertex = node;
                if let Some(prev_clock) = c.iter().filter(|clk| **clk < this_clock).last() {
                    let weight = graph.upsert_edge(
                        GraphSegment {
                            name: node.name,
                            clock: *prev_clock,
                        },
                        self_vertex,
                        0,
                    );
                    *weight += 1;
                }
            } else {
                let weight = graph.upsert_edge(node, self_vertex, 0);
                *weight += 1;
            }
        }
    }
    Ok(())
}

/// `overlay` provides a state-like graph, separating events by id,
/// and building a graph whose edges point to events that at some
/// point came after the source event.
pub fn overlay<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphWithWeightsBuilder<'a, Node = &'a str, Weight = usize>,
    E: std::error::Error,
{
    let mut prev_event = None;
    let mut last_seg_id = None;
    let mut last_ev_by_loc_clk: HashMap<(u32, u32), &str> = HashMap::new();
    let mut current_loc_clock = None;
    let mut first_event = true;
    let mut clock_set = Vec::new();
    let mut missing_segs = Vec::new();

    for res in log {
        let event: ReportEvent = res.map_err(|e| Error::ItemError(format!("{}", e)))?;

        if event.lc_tracer_id.is_none() && event.lc_clock.is_none() {
            if let Some(meta_ev) = cfg.events.get(
                &event
                    .event_id
                    .ok_or_else(|| Error::InconsistentData("missing event id"))?,
            ) {
                let weight = graph.upsert_node(&meta_ev.name, 0);
                *weight += 1;

                if first_event {
                    for (loc, clk) in clock_set.iter() {
                        match last_ev_by_loc_clk.get(&(*loc, *clk)) {
                            Some(e) => {
                                let weight = graph.upsert_edge(e, &meta_ev.name, 0);
                                *weight += 1;
                            }
                            None => missing_segs.push((*loc, *clk, &meta_ev.name)),
                        }
                    }
                    first_event = false;
                    clock_set.clear();
                } else if let Some(pe) = prev_event {
                    let weight = graph.upsert_edge(pe, &meta_ev.name, 0);
                    *weight += 1;
                }
                prev_event = Some(&meta_ev.name);
            }
        } else {
            let tracer = event
                .lc_tracer_id
                .ok_or_else(|| Error::InconsistentData("missing tracer id"))?;
            let clock = event
                .lc_clock
                .ok_or_else(|| Error::InconsistentData("missing logical clock"))?;
            if Some(event.segment_id) != last_seg_id && event.tracer_id == tracer {
                if let Some((loc, clock)) = current_loc_clock {
                    if let Some(prev) = prev_event {
                        last_ev_by_loc_clk.insert((loc, clock), prev);
                    }
                }
                current_loc_clock = Some((tracer, clock));
                last_seg_id = Some(event.segment_id);
                first_event = true;
            } else {
                clock_set.push((tracer, clock));
            }
        }
    }

    for (loc, clk, ev) in missing_segs {
        if let Some(e) = last_ev_by_loc_clk.get(&(loc, clk)) {
            let weight = graph.upsert_edge(e, ev, 0);
            *weight += 1;
        }
    }

    Ok(())
}

/// `topo` isolates tracers by id and draws edges showing which
/// instrumented components in a system are interacting.
pub fn topo<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphWithWeightsBuilder<'a, Node = &'a str, Weight = usize>,
    E: std::error::Error,
{
    let mut self_vertex = "";

    for res in log {
        let event: ReportEvent = res.map_err(|e| Error::ItemError(format!("{}", e)))?;

        if event.lc_tracer_id.is_some() && event.lc_clock.is_some() {
            if event.tracer_id
                == event
                    .lc_tracer_id
                    .ok_or_else(|| Error::InconsistentData("missing tracer id"))?
            {
                self_vertex = &cfg
                    .tracers
                    .get(&event.tracer_id)
                    .ok_or_else(|| Error::InconsistentData("unknown tracer_id"))?
                    .name;
                let weight = graph.upsert_node(self_vertex, 0);
                *weight += 1;
            } else {
                let weight = graph.upsert_edge(
                    &cfg.tracers
                        .get(
                            &event
                                .lc_tracer_id
                                .ok_or_else(|| Error::InconsistentData("missing tracer_id"))?,
                        )
                        .ok_or_else(|| Error::InconsistentData("unknown tracer_id"))?
                        .name,
                    self_vertex,
                    0,
                );
                *weight += 1;
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use crate::{digraph::Digraph, graph_event::*, meta::*};

    use super::{Cfg, Error};

    //   1
    //  / \   |
    // 2   3  |
    //  \ /   V
    //   4
    fn diamond() -> (Cfg, Vec<ReportEvent>) {
        (
            Cfg {
                tracers: vec![
                    (
                        1,
                        TracerMeta {
                            id: 1,
                            name: "one".to_string(),
                            description: "one".to_string(),
                            file: String::new(),
                            function: String::new(),
                            line: 0,
                        },
                    ),
                    (
                        2,
                        TracerMeta {
                            id: 2,
                            name: "two".to_string(),
                            description: "two".to_string(),
                            file: String::new(),
                            function: String::new(),
                            line: 0,
                        },
                    ),
                    (
                        3,
                        TracerMeta {
                            id: 3,
                            name: "three".to_string(),
                            description: "three".to_string(),
                            file: String::new(),
                            function: String::new(),
                            line: 0,
                        },
                    ),
                    (
                        4,
                        TracerMeta {
                            id: 4,
                            name: "four".to_string(),
                            description: "four".to_string(),
                            file: String::new(),
                            function: String::new(),
                            line: 0,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                events: vec![
                    (
                        1,
                        EventMeta {
                            id: 1,
                            name: "one".to_string(),
                            type_hint: None,
                            tags: String::new(),
                            description: String::new(),
                            file: String::new(),
                            line: None,
                        },
                    ),
                    (
                        2,
                        EventMeta {
                            id: 2,
                            name: "two".to_string(),
                            type_hint: None,
                            tags: String::new(),
                            description: String::new(),
                            file: String::new(),
                            line: None,
                        },
                    ),
                    (
                        3,
                        EventMeta {
                            id: 3,
                            name: "three".to_string(),
                            type_hint: None,
                            tags: String::new(),
                            description: String::new(),
                            file: String::new(),
                            line: None,
                        },
                    ),
                    (
                        4,
                        EventMeta {
                            id: 4,
                            name: "four".to_string(),
                            type_hint: None,
                            tags: String::new(),
                            description: String::new(),
                            file: String::new(),
                            line: None,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            vec![
                // 1
                ReportEvent {
                    segment_id: 0,
                    segment_index: 0,
                    tracer_id: 1,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(1),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 0,
                    segment_index: 2,
                    tracer_id: 1,
                    event_id: Some(1),
                    event_payload: None,
                    lc_tracer_id: None,
                    lc_clock: None,
                },
                // 2
                ReportEvent {
                    segment_id: 1,
                    segment_index: 0,
                    tracer_id: 2,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(2),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 1,
                    segment_index: 1,
                    tracer_id: 2,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(1),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 1,
                    segment_index: 2,
                    tracer_id: 2,
                    event_id: Some(2),
                    event_payload: None,
                    lc_tracer_id: None,
                    lc_clock: None,
                },
                // 3
                ReportEvent {
                    segment_id: 2,
                    segment_index: 0,
                    tracer_id: 3,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(3),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 2,
                    segment_index: 1,
                    tracer_id: 3,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(1),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 2,
                    segment_index: 2,
                    tracer_id: 3,
                    event_id: Some(3),
                    event_payload: None,
                    lc_tracer_id: None,
                    lc_clock: None,
                },
                // 4
                ReportEvent {
                    segment_id: 3,
                    segment_index: 0,
                    tracer_id: 4,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(4),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 3,
                    segment_index: 1,
                    tracer_id: 4,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(2),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 3,
                    segment_index: 2,
                    tracer_id: 4,
                    event_id: None,
                    event_payload: None,
                    lc_tracer_id: Some(3),
                    lc_clock: Some(1),
                },
                ReportEvent {
                    segment_id: 3,
                    segment_index: 3,
                    tracer_id: 4,
                    event_id: Some(4),
                    event_payload: None,
                    lc_tracer_id: None,
                    lc_clock: None,
                },
            ],
        )
    }

    #[test]
    fn complete() {
        use super::GraphBuilder;
        let (cfg, events) = diamond();
        let mut graph = Digraph::new();
        super::complete(
            &cfg,
            &mut graph,
            events.clone().into_iter().map(Ok::<_, Error>),
        )
        .unwrap();

        let mut expected = Digraph::new();
        let one = GraphEvent::Event {
            name: "one",
            location: "one",
            clock: 1,
            clock_offset: 2,
        };
        let two = GraphEvent::Event {
            name: "two",
            location: "two",
            clock: 1,
            clock_offset: 2,
        };
        let three = GraphEvent::Event {
            name: "three",
            location: "three",
            clock: 1,
            clock_offset: 2,
        };
        let four = GraphEvent::Event {
            name: "four",
            location: "four",
            clock: 1,
            clock_offset: 3,
        };
        expected.add_node(one);
        expected.add_node(two);
        expected.add_node(three);
        expected.add_node(four);

        expected.add_edge(one, two);
        expected.add_edge(one, three);
        expected.add_edge(two, four);
        expected.add_edge(three, four);

        assert_eq!(graph, expected, "\n{:#?}\n{:#?}", graph, expected);
    }

    #[test]
    fn segments() {
        use super::GraphWithWeightsBuilder;
        let (cfg, events) = diamond();
        let mut graph = Digraph::new();
        super::segments(&cfg, &mut graph, events.into_iter().map(Ok::<_, Error>)).unwrap();

        let mut expected = Digraph::new();
        let one = GraphSegment {
            name: "one",
            clock: 1,
        };
        let two = GraphSegment {
            name: "two",
            clock: 1,
        };
        let three = GraphSegment {
            name: "three",
            clock: 1,
        };
        let four = GraphSegment {
            name: "four",
            clock: 1,
        };
        expected.add_node(one, 3);
        expected.add_node(two, 2);
        expected.add_node(three, 2);
        expected.add_node(four, 1);

        expected.add_edge(one, two, 1);
        expected.add_edge(one, three, 1);
        expected.add_edge(two, four, 1);
        expected.add_edge(three, four, 1);

        assert_eq!(graph, expected, "\n{:#?}\n{:#?}", graph, expected);
    }

    #[test]
    fn overlay() {
        use super::GraphWithWeightsBuilder;
        let (cfg, events) = diamond();
        let mut graph = Digraph::new();
        super::overlay(
            &cfg,
            &mut graph,
            events.clone().into_iter().map(Ok::<_, Error>),
        )
        .unwrap();

        let mut expected = Digraph::new();
        let one = "one";
        let two = "two";
        let three = "three";
        let four = "four";
        expected.add_node(one, 1);
        expected.add_node(two, 1);
        expected.add_node(three, 1);
        expected.add_node(four, 1);

        expected.add_edge(one, two, 1);
        expected.add_edge(one, three, 1);
        expected.add_edge(two, four, 1);
        expected.add_edge(three, four, 1);

        assert_eq!(graph, expected, "\n{:#?}\n{:#?}", graph, expected);
    }

    #[test]
    fn topo() {
        use super::GraphWithWeightsBuilder;
        let (cfg, events) = diamond();
        let mut graph = Digraph::new();
        super::topo(
            &cfg,
            &mut graph,
            events.clone().into_iter().map(Ok::<_, Error>),
        )
        .unwrap();

        let mut expected = Digraph::new();
        let one = "one";
        let two = "two";
        let three = "three";
        let four = "four";
        expected.add_node(one, 1);
        expected.add_node(two, 1);
        expected.add_node(three, 1);
        expected.add_node(four, 1);

        expected.add_edge(one, two, 1);
        expected.add_edge(one, three, 1);
        expected.add_edge(two, four, 1);
        expected.add_edge(three, four, 1);

        assert_eq!(graph, expected, "\n{:#?}\n{:#?}", graph, expected);
    }
}
