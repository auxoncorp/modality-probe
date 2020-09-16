pub mod complete {
    use std::{
        collections::{HashMap, HashSet},
        ops::{Deref, DerefMut},
    };

    use serde::{
        ser::{SerializeSeq, Serializer},
        Serialize,
    };

    use crate::export::graph::EventMeta;

    pub const TEMP: &'static str = "digraph G \\{
    node [ color = \"#ffffff\" style = filled ]
    edge [ color = \"#ffffff\" ]
    {{ for comp in components }}
    subgraph cluster_{ comp.cluster_idx } \\{
        label = \"{ comp.name }\"
        style = filled
        color = \"{ comp.fill_color }\"
        {{ for probe in comp.probes }}
        subgraph cluster_{ probe.cluster_idx } \\{
            label = \"{ probe.name }\"
            fontcolor = \"#ffffff\"
            rank = same
            style = filled
            color = \"{ probe.fill_color }\"
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

    pub struct ComponentSet(HashMap<String, Component>);

    impl ComponentSet {
        pub fn new() -> Self {
            ComponentSet(HashMap::new())
        }
    }

    impl Serialize for ComponentSet {
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

    impl Deref for ComponentSet {
        type Target = HashMap<String, Component>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl DerefMut for ComponentSet {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    pub struct ProbeSet(HashMap<String, Probe>);

    impl ProbeSet {
        pub fn new() -> Self {
            ProbeSet(HashMap::new())
        }
    }

    impl Serialize for ProbeSet {
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

    impl Deref for ProbeSet {
        type Target = HashMap<String, Probe>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl DerefMut for ProbeSet {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    pub struct EdgeSet(HashSet<Edge>);

    impl EdgeSet {
        pub fn new() -> Self {
            EdgeSet(HashSet::new())
        }
    }

    impl Deref for EdgeSet {
        type Target = HashSet<Edge>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl DerefMut for EdgeSet {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl Serialize for EdgeSet {
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
        pub components: ComponentSet,
        pub edges: EdgeSet,
    }

    #[derive(Serialize)]
    pub struct Component {
        pub cluster_idx: usize,
        pub fill_color: String,
        pub name: String,
        pub probes: ProbeSet,
    }

    #[derive(Serialize)]
    pub struct Probe {
        pub cluster_idx: usize,
        pub name: String,
        pub raw_id: u32,
        pub fill_color: String,
        pub events: Vec<Event>,
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
        pub seq: u64,
        pub seq_idx: usize,
    }

    #[derive(PartialEq, Eq, Hash, Serialize)]
    pub struct Edge {
        pub from: Event,
        pub to: Event,
    }
}
