use std::{collections::HashMap, path::PathBuf};

use serde::{Deserialize, Serialize};
use uuid::Uuid;

use modality_probe::{EventId, ProbeId};

use crate::{component::Component, events::Events, give_up, hopefully, hopefully_ok};

/// A row in the events.csv for a component.
#[derive(PartialEq, Eq, Debug, Clone, Deserialize, Hash, Serialize)]
pub struct EventMeta {
    pub component_id: Uuid,
    pub id: u32,
    pub name: String,
    pub type_hint: Option<String>,
    pub tags: String,
    pub description: String,
    pub file: String,
    pub line: String,
}

/// A row in probes.csv for a component.
#[derive(PartialEq, Serialize, Debug, Clone, Deserialize)]
pub struct ProbeMeta {
    pub component_id: Uuid,
    pub tags: String,
    pub id: u32,
    pub name: String,
    pub description: String,
    pub file: String,
    pub line: String,
}

/// Something that can mete out probe, component, and event metadata
/// on demand.
pub trait MetaMeter {
    fn probe_component_id(&self, id: &ProbeId) -> Option<Uuid>;
    fn probe_component_name(&self, id: &ProbeId) -> Option<String>;
    fn probe_tags(&self, id: &ProbeId) -> Option<Vec<String>>;
    fn probe_name(&self, id: &ProbeId) -> Option<String>;
    fn probe_description(&self, id: &ProbeId) -> Option<String>;
    fn probe_file(&self, id: &ProbeId) -> Option<String>;
    fn probe_line(&self, id: &ProbeId) -> Option<String>;

    fn event_tags(&self, probe: &ProbeId, id: &EventId) -> Option<Vec<String>>;
    fn event_type_hint(&self, probe: &ProbeId, id: &EventId) -> Option<String>;
    fn event_name(&self, probe: &ProbeId, id: &EventId) -> Option<String>;
    fn event_description(&self, probe: &ProbeId, id: &EventId) -> Option<String>;
    fn event_file(&self, probe: &ProbeId, id: &EventId) -> Option<String>;
    fn event_line(&self, probe: &ProbeId, id: &EventId) -> Option<String>;
}

impl MetaMeter for Cfg {
    fn probe_component_name(&self, id: &ProbeId) -> Option<String> {
        self.probes_to_components
            .get(&id.get_raw())
            .map(|id| self.component_names.get(&id.to_string()).cloned())
            .flatten()
    }

    fn probe_component_id(&self, id: &ProbeId) -> Option<Uuid> {
        self.probes.get(&id.get_raw()).map(|p| p.component_id)
    }

    fn probe_tags(&self, id: &ProbeId) -> Option<Vec<String>> {
        self.probes
            .get(&id.get_raw())
            .map(|p| p.tags.split(';').map(|t| t.to_string()).collect())
    }

    fn probe_name(&self, id: &ProbeId) -> Option<String> {
        self.probes.get(&id.get_raw()).map(|p| p.name.clone())
    }

    fn probe_description(&self, id: &ProbeId) -> Option<String> {
        self.probes
            .get(&id.get_raw())
            .map(|p| p.description.clone())
    }

    fn probe_file(&self, id: &ProbeId) -> Option<String> {
        self.probes.get(&id.get_raw()).map(|p| p.file.clone())
    }

    fn probe_line(&self, id: &ProbeId) -> Option<String> {
        self.probes.get(&id.get_raw()).map(|p| p.line.clone())
    }

    fn event_tags(&self, probe: &ProbeId, id: &EventId) -> Option<Vec<String>> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|e| e.tags.split(';').map(|t| t.to_string()).collect())
            })
            .flatten()
    }

    fn event_type_hint(&self, probe: &ProbeId, id: &EventId) -> Option<String> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|e| e.type_hint.as_ref().map(|th| th.to_string()))
                    .flatten()
            })
            .flatten()
    }

    fn event_name(&self, probe: &ProbeId, id: &EventId) -> Option<String> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|p| p.name.clone())
            })
            .flatten()
    }

    fn event_description(&self, probe: &ProbeId, id: &EventId) -> Option<String> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|p| p.description.clone())
            })
            .flatten()
    }

    fn event_file(&self, probe: &ProbeId, id: &EventId) -> Option<String> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|p| p.file.clone())
            })
            .flatten()
    }

    fn event_line(&self, probe: &ProbeId, id: &EventId) -> Option<String> {
        self.probes_to_components
            .get(&probe.get_raw())
            .map(|comp| {
                self.events
                    .get(&(*comp, id.get_raw()))
                    .map(|p| p.line.clone())
            })
            .flatten()
    }
}

#[derive(Debug)]
pub struct Cfg {
    pub probes: HashMap<u32, ProbeMeta>,
    pub events: HashMap<(Uuid, u32), EventMeta>,
    pub probes_to_components: HashMap<u32, Uuid>,
    pub component_names: HashMap<String, String>,
}

pub fn assemble_components(
    comp_dirs: &mut Vec<PathBuf>,
) -> Result<Cfg, Box<dyn std::error::Error>> {
    let mut probes = HashMap::new();
    let mut probes_to_components = HashMap::new();
    let mut events = HashMap::new();
    let mut component_names = HashMap::new();

    let mut event_files = Vec::new();
    let mut probe_files = Vec::new();
    for dir in comp_dirs.iter_mut() {
        dir.push("probes.csv");
        probe_files.push(dir.clone());
        dir.pop();
        dir.push("events.csv");
        event_files.push(dir.clone());
    }
    for pf in probe_files.iter_mut() {
        let mut pr_rdr = hopefully!(
            csv::Reader::from_path(pf.clone()),
            format!("Failed to open the probes file at {}", pf.display(),)
        )?;
        for res in pr_rdr.deserialize() {
            let p: ProbeMeta = hopefully!(res, "Failed to deserialize a probe row")?;
            pf.pop();
            pf.push("Component.toml");
            let comp = Component::from_toml(&pf);
            probes.insert(p.id, p.clone());
            probes_to_components.insert(p.id, comp.id.0);
            component_names.insert(comp.id.0.to_string(), comp.name);
        }
    }
    for ef in event_files.iter_mut() {
        let mut ev_rdr = hopefully!(
            csv::Reader::from_path(ef.clone()),
            format!("Failed to open the events file at {}", ef.display())
        )?;
        for res in ev_rdr.deserialize() {
            let e: EventMeta = hopefully!(res, "Failed to deserialize an event row")?;
            ef.pop();
            ef.push("Component.toml");
            let comp = Component::from_toml(&ef);
            events.insert((comp.id.0, e.id), e.clone());
        }
    }

    add_internal_events(&mut events);

    Ok(Cfg {
        events,
        probes,
        probes_to_components,
        component_names,
    })
}

pub fn get_event_meta<'a>(
    cfg: &'a Cfg,
    pid: &ProbeId,
    eid: &EventId,
) -> Result<&'a EventMeta, Box<dyn std::error::Error>> {
    let comp_id = hopefully_ok!(
        cfg.probes_to_components.get(&pid.get_raw()),
        format!(
            "Unable to find a matching component for probe {}",
            pid.get_raw()
        )
    )?;
    Ok(hopefully_ok!(
        cfg.events.get(&(*comp_id, eid.get_raw())),
        format!(
            "Unable to find metadata for event {} in component {}",
            eid.get_raw(),
            comp_id
        )
    )?)
}

pub fn parsed_payload(
    th: Option<&str>,
    pl: Option<u32>,
) -> Result<Option<String>, Box<dyn std::error::Error>> {
    match (th, pl) {
        (Some("i8"), Some(pl)) => Ok(Some(format!("{}", pl as i8))),
        (Some("i16"), Some(pl)) => Ok(Some(format!("{}", pl as i16))),
        (Some("i32"), Some(pl)) => Ok(Some(format!("{}", pl as i32))),
        (Some("u8"), Some(pl)) => Ok(Some(format!("{}", pl as u8))),
        (Some("u16"), Some(pl)) => Ok(Some(format!("{}", pl as u16))),
        (Some("u32"), Some(pl)) => Ok(Some(format!("{}", pl as u32))),
        (Some("f32"), Some(pl)) => Ok(Some(format!("{}", f32::from_bits(pl)))),
        (Some("bool"), Some(pl)) => Ok(Some(format!("{}", pl != 0))),
        (Some(th), Some(_)) => give_up!(format!("{} is not a valid type hint", th)),
        (None, Some(pl)) => Ok(Some(pl.to_string())),
        (Some(_), None) => Ok(None),
        (None, None) => Ok(None),
    }
}

fn add_internal_events(events: &mut HashMap<(Uuid, u32), EventMeta>) {
    let nil_uuid = Uuid::nil();
    for ie in Events::internal_events() {
        let ev = EventMeta {
            component_id: nil_uuid,
            id: ie.id.0,
            name: ie.name,
            type_hint: if ie.type_hint.is_empty() {
                None
            } else {
                Some(ie.type_hint)
            },
            tags: ie.tags,
            description: ie.description,
            file: ie.file,
            line: ie.line,
        };
        events.insert((nil_uuid, ie.id.0), ev.clone());
    }
}

#[cfg(test)]
mod test {
    use std::{fs, fs::File, io::Write};

    use tempfile::tempdir;
    use uuid::Uuid;

    use crate::meta::{EventMeta, ProbeMeta};

    const COMP_ONE_CONTENT: &'static str = r#"
name = "one"
id = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca1"
"#;
    const COMP_TWO_CONTENT: &'static str = r#"
name = "two"
id = "bba61171-e4b5-4db4-8cbb-8b4f4a581ca2"
"#;
    const PROBE_ONE_CONTENT: &'static str = "
component_id,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,PROBE_ONE,probe one,example,examples/event-recording.rs,26";
    const PROBE_TWO_CONTENT: &'static str = "
component_id,id,name,description,tags,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,PROBE_TWO,probe two,example,examples/event-recording.rs,26";

    const EVENT_ONE_CONTENT: &'static str = "
component_id,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb1,1,TEST_ONE,test event one,,,,26
";
    const EVENT_TWO_CONTENT: &'static str = "
component_id,id,name,description,tags,type_hint,file,line
bba61171-e4b5-4db4-8cbb-8b4f4a581cb2,2,TEST_TWO,test event two,,,,36
";

    #[test]
    fn comp_assembly() {
        let mut tmp_one = tempdir().unwrap().into_path();
        let mut tmp_two = tempdir().unwrap().into_path();

        {
            tmp_one.push("Component.toml");
            let mut comp_one = File::create(&tmp_one).unwrap();
            write!(comp_one, "{}", COMP_ONE_CONTENT).unwrap();
            tmp_one.pop();
            tmp_one.push("probes.csv");
            let mut probe_one = File::create(&tmp_one).unwrap();
            write!(probe_one, "{}", PROBE_ONE_CONTENT).unwrap();
            tmp_one.pop();
            tmp_one.push("events.csv");
            let mut event_one = File::create(&tmp_one).unwrap();
            write!(event_one, "{}", EVENT_ONE_CONTENT).unwrap();

            tmp_two.push("Component.toml");
            let mut comp_two = File::create(&tmp_two).unwrap();
            write!(comp_two, "{}", COMP_TWO_CONTENT).unwrap();
            tmp_two.pop();
            tmp_two.push("probes.csv");
            let mut probe_two = File::create(&tmp_two).unwrap();
            write!(probe_two, "{}", PROBE_TWO_CONTENT).unwrap();
            tmp_two.pop();
            tmp_two.push("events.csv");
            let mut event_two = File::create(&tmp_two).unwrap();
            write!(event_two, "{}", EVENT_TWO_CONTENT).unwrap();

            let expected_probes = vec![
                (
                    1,
                    ProbeMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1")
                            .unwrap(),
                        id: 1,
                        name: "PROBE_ONE".to_string(),
                        description: "probe one".to_string(),
                        file: "examples/event-recording.rs".to_string(),
                        line: "26".to_string(),
                        tags: "example".to_string(),
                    },
                ),
                (
                    2,
                    ProbeMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2")
                            .unwrap(),
                        id: 2,
                        name: "PROBE_TWO".to_string(),
                        description: "probe two".to_string(),
                        file: "examples/event-recording.rs".to_string(),
                        line: "26".to_string(),
                        tags: "example".to_string(),
                    },
                ),
            ]
            .into_iter()
            .collect();

            let mut expected_events = vec![
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca1").unwrap(),
                        1,
                    ),
                    EventMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb1")
                            .unwrap(),
                        id: 1,
                        name: "TEST_ONE".to_string(),
                        description: "test event one".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: "26".to_string(),
                    },
                ),
                (
                    (
                        Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581ca2").unwrap(),
                        2,
                    ),
                    EventMeta {
                        component_id: Uuid::parse_str("bba61171-e4b5-4db4-8cbb-8b4f4a581cb2")
                            .unwrap(),
                        id: 2,
                        name: "TEST_TWO".to_string(),
                        description: "test event two".to_string(),
                        type_hint: None,
                        tags: String::new(),
                        file: String::new(),
                        line: "36".to_string(),
                    },
                ),
            ]
            .into_iter()
            .collect();

            super::add_internal_events(&mut expected_events);

            tmp_one.pop();
            tmp_two.pop();
            let cfg =
                super::assemble_components(&mut vec![tmp_one.clone(), tmp_two.clone()]).unwrap();

            assert_eq!(&cfg.probes, &expected_probes);
            assert_eq!(&cfg.events, &expected_events);
        }

        fs::remove_dir_all(&tmp_one).unwrap();
        fs::remove_dir_all(&tmp_two).unwrap();
    }
}
