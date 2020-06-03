use std::{collections::HashMap, hash::Hash};

use err_derive::Error;

pub mod digraph;
pub mod graph_event;
pub mod meta;

use crate::{
    graph_event::{GraphEvent, GraphSegment},
    meta::{EventMeta, ReportEvent, TracerMeta},
};

#[derive(Debug, Error)]
pub enum Error {
    #[error(display = "writing dot failed: {}", _0)]
    Io(String),
    #[error(display = "An item in the log iterator was an error variant: {}", _0)]
    ItemError(String),
    #[error(display = "Encountered an inconsistency in the data: {}", _0)]
    InconsistentData(&'static str),
}

pub trait GraphBuilder<'a> {
    type Node: Eq + Hash + Clone + Copy;

    fn add_node(&mut self, node: Self::Node);
    fn add_edge(&mut self, from: Self::Node, to: Self::Node);
}

pub trait GraphWithWeightsBuilder<'a> {
    type Node: Eq + Hash + Clone + Copy;
    type Weight: Clone + Copy;

    fn add_node(&mut self, node: Self::Node, weight: Self::Weight);
    fn upsert_node(&mut self, node: Self::Node, weight: Self::Weight) -> &mut Self::Weight;
    fn add_edge(&mut self, from: Self::Node, to: Self::Node, weight: Self::Weight);
    fn upsert_edge(
        &mut self,
        from: Self::Node,
        to: Self::Node,
        weight: Self::Weight,
    ) -> &mut Self::Weight;
}

pub struct Cfg {
    pub tracers: HashMap<u32, TracerMeta>,
    pub events: HashMap<u32, EventMeta>,
}

pub fn complete<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphBuilder<'a, Node = GraphEvent<'a>>,
    E: std::error::Error,
{
    let mut prev_event = None;
    let mut last_seg_id = 0;
    let mut last_ev_by_loc_clk: HashMap<(u32, u32), GraphEvent> = HashMap::new();
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
                if let Some(pe) = prev_event {
                    graph.add_edge(pe, node);
                }

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
            if event.segment_id != last_seg_id && event.tracer_id == tracer {
                if let Some((loc, clock)) = current_loc_clock {
                    if let Some(prev) = prev_event {
                        last_ev_by_loc_clk.insert((loc, clock), prev);
                    }
                }
                current_loc_clock = Some((tracer, clock));
                last_seg_id = event.segment_id;
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

pub fn segments<'a, G, E>(
    cfg: &'a Cfg,
    graph: &mut G,
    log: impl Iterator<Item = Result<ReportEvent, E>>,
) -> Result<(), Error>
where
    G: GraphBuilder<'a, Node = GraphSegment<'a>>,
    E: std::error::Error,
{
    let mut self_vertex = GraphSegment::default();
    let mut self_clocks = HashMap::new();

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
            graph.add_node(node);
            if event.tracer_id
                == event
                    .lc_tracer_id
                    .ok_or_else(|| Error::InconsistentData("missing tracer id"))?
            {
                let this_clock = event
                    .lc_clock
                    .ok_or_else(|| Error::InconsistentData("missing logical clock"))?;
                let c = self_clocks.entry(tracer_name).or_insert(Vec::new());
                c.push(this_clock);
                c.sort();
                self_vertex = node;
                if let Some(prev_clock) = c.iter().filter(|clk| **clk < this_clock).last() {
                    graph.add_edge(
                        GraphSegment {
                            name: node.name,
                            clock: *prev_clock,
                        },
                        self_vertex,
                    );
                }
            } else {
                graph.add_edge(node, self_vertex);
            }
        }
    }
    Ok(())
}

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
    let mut last_seg_id = 0;
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
                if let Some(pe) = prev_event {
                    let weight = graph.upsert_edge(pe, &meta_ev.name, 0);
                    *weight += 1;
                }

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
            if event.segment_id != last_seg_id && event.tracer_id == tracer {
                if let Some((loc, clock)) = current_loc_clock {
                    if let Some(prev) = prev_event {
                        last_ev_by_loc_clk.insert((loc, clock), prev);
                    }
                }
                current_loc_clock = Some((tracer, clock));
                last_seg_id = event.segment_id;
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
                graph.add_node(self_vertex, 0);
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
