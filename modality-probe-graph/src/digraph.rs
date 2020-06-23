//! A simple directed graph type that compliles node and edge lists.

use std::{collections::HashMap, fmt::Write, hash::Hash};

use crate::Error;

#[derive(Debug, PartialEq, Eq, Default)]
pub struct Digraph<N, W>
where
    N: Eq + Hash + Clone + Copy,
    W: Eq + Clone + Copy,
{
    nodes: HashMap<N, W>,
    edges: HashMap<(N, N), W>,
}

impl<N, W> Digraph<N, W>
where
    N: Eq + Hash + Clone + Copy,
    W: Eq + Clone + Copy,
{
    /// Construct an empty graph.
    pub fn new() -> Self {
        Digraph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    /// Output the graph as dot, use the given functions to format
    /// node ids, node attributes, and edge attributes.
    pub fn to_dot<F, G, H>(
        &self,
        node_id_fmt: F,
        node_attr_fmt: G,
        edge_fmt: H,
    ) -> Result<String, Error>
    where
        F: Fn(&N, &W) -> Result<String, String>,
        G: Fn(&N, &W) -> Result<String, String>,
        H: Fn(&N, &N, &W) -> Result<String, String>,
    {
        let mut out = String::new();
        writeln!(&mut out, "digraph G {{").map_err(|e| Error::Io(e.to_string()))?;
        for (n, w) in self.nodes.iter() {
            writeln!(
                out,
                "    {} [{}]",
                node_id_fmt(n, w).map_err(Error::Io)?,
                node_attr_fmt(n, w).map_err(Error::Io)?
            )
            .map_err(|e| Error::Io(e.to_string()))?;
        }
        for ((from, to), weight) in self.edges.iter() {
            writeln!(
                out,
                "    {} -> {} [{}]",
                node_id_fmt(from, weight).map_err(Error::Io)?,
                node_id_fmt(to, weight).map_err(Error::Io)?,
                edge_fmt(from, to, weight).map_err(Error::Io)?
            )
            .map_err(|e| Error::Io(e.to_string()))?;
        }
        writeln!(out, "}}").map_err(|e| crate::Error::Io(e.to_string()))?;
        Ok(out)
    }
}

impl<'a, N> crate::GraphBuilder<'a> for Digraph<N, ()>
where
    N: Eq + Hash + Clone + Copy,
{
    type Node = N;

    fn add_node(&mut self, val: N) {
        self.nodes.insert(val, ());
    }

    fn add_edge(&mut self, from: N, to: N) {
        self.edges.insert((from, to), ());
    }
}

impl<'a, N, W> crate::GraphWithWeightsBuilder<'a> for Digraph<N, W>
where
    N: Eq + Hash + Clone + Copy,
    W: Eq + Clone + Copy,
{
    type Node = N;
    type Weight = W;

    fn add_node(&mut self, val: N, weight: W) {
        self.nodes.insert(val, weight);
    }

    fn upsert_node(&mut self, val: N, weight: W) -> &mut W {
        self.nodes.entry(val).or_insert(weight)
    }

    fn add_edge(&mut self, from: N, to: N, weight: W) {
        self.edges.insert((from, to), weight);
    }

    fn upsert_edge(&mut self, from: N, to: N, weight: W) -> &mut W {
        self.edges.entry((from, to)).or_insert(weight)
    }
}
