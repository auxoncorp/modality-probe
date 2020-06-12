use std::{collections::HashMap, fmt::Write, hash::Hash};

pub struct Digraph<N, W> {
    nodes: HashMap<N, W>,
    edges: HashMap<(N, N), W>,
}

impl<N, W> Digraph<N, W>
where
    N: Eq + Hash + Clone + Copy,
    W: Eq + Clone + Copy,
{
    pub fn new() -> Self {
        Digraph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    pub fn to_dot<F, G, H>(&self, node_id_fmt: F, node_attr_fmt: G, edge_fmt: H) -> String
    where
        F: Fn(&N, &W) -> String,
        G: Fn(&N, &W) -> String,
        H: Fn(&N, &N, &W) -> String,
    {
        let mut out = String::new();
        writeln!(&mut out, "digraph G {{");
        for (n, w) in self.nodes.iter() {
            writeln!(out, "    {} [{}]", node_id_fmt(n, w), node_attr_fmt(n, w));
        }
        for ((from, to), weight) in self.edges.iter() {
            writeln!(
                out,
                "    {} -> {} [{}]",
                node_id_fmt(from, weight),
                node_id_fmt(to, weight),
                edge_fmt(from, to, weight)
            );
        }
        writeln!(out, "}}");
        out
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
