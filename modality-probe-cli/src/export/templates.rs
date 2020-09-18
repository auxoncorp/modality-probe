use std::{
    collections::{hash_map::DefaultHasher, HashMap, HashSet},
    fmt::Write,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

use serde::{
    ser::{SerializeSeq, Serializer},
    Serialize,
};
use serde_json::Value;

use super::graph::EventMeta;

#[derive(Serialize)]
pub struct Component<E: Serialize> {
    pub cluster_idx: usize,
    pub name: String,
    pub probes: ProbeSet<E>,
}

#[derive(Serialize)]
pub struct Probe<E: Serialize> {
    pub cluster_idx: usize,
    pub name: String,
    pub raw_id: u32,
    pub events: Vec<E>,
}
pub struct ComponentSet<E: Serialize>(HashMap<String, Component<E>>);

impl<E: Serialize> ComponentSet<E> {
    pub fn new() -> Self {
        ComponentSet(HashMap::new())
    }
}

impl<E: Serialize> Serialize for ComponentSet<E> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.values().len()))?;
        for comp in self.0.values() {
            seq.serialize_element(comp)?
        }
        seq.end()
    }
}

impl<E: Serialize> Deref for ComponentSet<E> {
    type Target = HashMap<String, Component<E>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Serialize> DerefMut for ComponentSet<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct ProbeSet<E: Serialize>(HashMap<String, Probe<E>>);

impl<E: Serialize> ProbeSet<E> {
    pub fn new() -> Self {
        ProbeSet(HashMap::new())
    }
}

impl<E: Serialize> Serialize for ProbeSet<E> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.values().len()))?;
        for probe in self.0.values() {
            seq.serialize_element(probe)?
        }
        seq.end()
    }
}

impl<E: Serialize> Deref for ProbeSet<E> {
    type Target = HashMap<String, Probe<E>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Serialize> DerefMut for ProbeSet<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct EdgeSet<E: Serialize>(HashSet<E>);

impl<E: Serialize> EdgeSet<E> {
    pub fn new() -> Self {
        EdgeSet(HashSet::new())
    }
}

impl<E: Serialize> Deref for EdgeSet<E> {
    type Target = HashSet<E>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Serialize> DerefMut for EdgeSet<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<E: Serialize> Serialize for EdgeSet<E> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for edge in self.0.iter() {
            seq.serialize_element(&edge)?
        }
        seq.end()
    }
}

#[derive(Serialize)]
pub struct Context {
    pub components: ComponentSet<Event>,
    pub edges: EdgeSet<Edge>,
}

#[derive(Hash, PartialEq, Eq, Serialize)]
pub struct Event {
    pub is_known: bool,
    pub meta: Option<EventMeta>,
    pub has_payload: bool,
    pub payload: Option<String>,
    pub raw_id: u32,
    pub raw_probe_id: u32,
    pub probe_name: String,
    pub clock: u32,
    pub seq: u64,
    pub seq_idx: usize,
}

#[derive(PartialEq, Eq, Hash, Serialize)]
pub struct Edge {
    pub from: Event,
    pub to: Event,
}

pub fn discrete_color_formatter(
    val: &Value,
    out: &mut String,
) -> Result<(), tinytemplate::error::Error> {
    let idx = match val {
        Value::Number(n) => {
            if n.is_u64() {
                (n.as_u64().unwrap() % 10) as usize
            } else {
                return Err(tinytemplate::error::Error::GenericError {
                    msg: "invalid value given to discrete_color_formatter".to_string(),
                });
            }
        }
        Value::String(s) => {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            (h.finish() % 10) as usize
        }
        _ => {
            return Err(tinytemplate::error::Error::GenericError {
                msg: "invalid value given to discrete_color_formatter".to_string(),
            })
        }
    };
    write!(out, "#{:x}", colorous::TABLEAU10[idx])?;
    Ok(())
}

pub fn gradient_color_formatter(
    val: &Value,
    out: &mut String,
) -> Result<(), tinytemplate::error::Error> {
    let idx = match val {
        Value::Number(n) => {
            if n.is_u64() {
                let n_float = n.as_u64().unwrap() as f64;
                (n_float % 10.0) / 10.0
            } else {
                return Err(tinytemplate::error::Error::GenericError {
                    msg: "invalid value given to discrete_color_formatter".to_string(),
                });
            }
        }
        Value::String(s) => {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            (h.finish() as f64 % 10.0) / 10.0
        }
        _ => {
            return Err(tinytemplate::error::Error::GenericError {
                msg: "invalid value given to discrete_color_formatter".to_string(),
            })
        }
    };
    write!(out, "#{:x}", colorous::GREYS.eval_continuous(idx))?;
    Ok(())
}

pub const COMPLETE: &'static str = "digraph G \\{
    node [ color = \"#ffffff\" style = filled ]
    edge [ color = \"#ffffff\" ]
    {{ for comp in components }}
    subgraph cluster_{ comp.cluster_idx } \\{
        label = \"{ comp.name }\"
        style = filled
        color = \"{ comp.name | gradient_color_formatter }\"
        {{ for probe in comp.probes }}
        subgraph cluster_{ probe.cluster_idx } \\{
            label = \"{ probe.name }\"
            fontcolor = \"#ffffff\"
            rank = same
            style = filled
            color = \"{ probe.name | discrete_color_formatter }\"
            {{ for event in probe.events }}
            {{ if event.is_known }}
            { event.meta.name }_{ event.probe_name }_{ event.seq }_{ event.seq_idx } [
                label        = \"{ event.meta.name }\"
                description  = \"{ event.meta.description }\"
                file         = \"{ event.meta.file }\"
                probe        = \"{ event.probe_name }\"
                tags         = \"{ event.meta.tags }\"{{ if event.has_payload }}
                payload      = { event.payload }{{ endif }}
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id }
            ];
            {{ else }}
            UNKNOWN_EVENT_{ event.probe_name }_{ event.seq }_{ event.seq_idx } [
                label        = \"UNKNOWN_EVENT_{ event.raw_id }\"
                probe        = \"{ event.probe_name }\"
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id }
            ];
            {{ endif }}
            {{ endfor }}
        }
        {{ endfor }}
    }
    {{ endfor }}

    {{ for edge in edges }}
    {{ if edge.from.is_known }}{ edge.from.meta.name }{{ else }}UNKNOWN_EVENT_{ edge.from.raw_id }{{ endif }}_{ edge.from.probe_name }_{ edge.from.seq }_{ edge.from.seq_idx } ->
    {{ if edge.to.is_known }}{ edge.to.meta.name }{{ else }}UNKNOWN_EVENT_{ edge.to.raw_id }{{ endif }}_{ edge.to.probe_name }_{ edge.to.seq }_{ edge.to.seq_idx };
    {{ endfor }}
}";

pub const INTERACTIONS: &'static str = "digraph G \\{
    node [ color = \"#ffffff\" style = filled ]
    edge [ color = \"#ffffff\" ]
    {{ for comp in components }}
    subgraph cluster_{ comp.cluster_idx } \\{
        label = \"{ comp.name }\"
        style = filled
        color = \"{ comp.name | gradient_color_formatter }\"
        {{ for probe in comp.probes }}
        subgraph cluster_{ probe.cluster_idx } \\{
            label = \"{ probe.name }\"
            fontcolor = \"#ffffff\"
            rank = same
            style = filled
            color = \"{ probe.name | discrete_color_formatter }\"
            {{ for event in probe.events }}
            { event.probe_name }_{ event.clock } [
                {{if event.is_known }}label        = \"{ event.meta.name }\"
                description  = \"{ event.meta.description }\"
                file         = \"{ event.meta.file }\"
                probe        = \"{ event.probe_name }\"
                tags         = \"{ event.meta.tags }\"{{ if event.has_payload }}
                payload      = { event.payload }{{ endif }}
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id }{{ else }}
                label        = \"UNKNOWN_EVENT_{ event.raw_id }\"
                probe        = \"{ event.probe_name }\"
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id } {{ endif }}
            ];
            {{ endfor}}
        }
        {{ endfor }}
    }
    {{ endfor }}

    {{ for edge in edges }}
    { edge.from.probe_name }_{ edge.from.clock } -> { edge.to.probe_name }_{ edge.to.clock }
    {{ endfor }}
}";

pub const STATES: &'static str = "digraph G \\{
    node [ color = \"#ffffff\" style = filled ]
    edge [ color = \"#ffffff\" ]
    {{ for comp in components }}
    subgraph cluster_{ comp.cluster_idx } \\{
        label = \"{ comp.name }\"
        style = filled
        color = \"{ comp.name | gradient_color_formatter }\"
        {{ for probe in comp.probes }}
        subgraph cluster_{ probe.cluster_idx } \\{
            label = \"{ probe.name }\"
            fontcolor = \"#ffffff\"
            rank = same
            style = filled
            color = \"{ probe.name | discrete_color_formatter }\"
            {{ for event in probe.events }}
            {{ if event.is_known }}{ event.meta.name }_AT_{ event.probe_name } [
                label        = \"{ event.meta.name } @ {event.probe_name }\"
                description  = \"{ event.meta.description }\"
                file         = \"{ event.meta.file }\"
                probe        = \"{ event.probe_name }\"
                tags         = \"{ event.meta.tags }\"{{ if event.has_payload }}
                payload      = { event.payload }{{ endif }}
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id }
            {{ else }}UNKNOWN_EVENT_{ event.raw_id }_AT_{ event.probe_name } [
                label        = \"UNKNOWN_EVENT_{ event.raw_id } @ { event.probe_name }\"
                probe        = \"{ event.probe_name }\"
                raw_event_id = { event.raw_id }
                raw_probe_id = { event.raw_probe_id } {{ endif }}
            ];
            {{ endfor}}
        }
        {{ endfor }}
    }
    {{ endfor }}

    {{ for edge in edges }}
    {{ if edge.from.is_known }}{ edge.from.meta.name }{{ else }}UNKNOWN_EVENT_{ event.raw_id }{{ endif }}_AT_{ edge.from.probe_name } ->
    {{ if edge.to.is_known }}{ edge.to.meta.name }{{ else }}UNKNOWN_EVENT_{ event.raw_id }{{ endif }}_AT_{ edge.to.probe_name }
    {{ endfor }}
}";
