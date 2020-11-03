use modality_probe_collector_common::{LogEntryData, ReportLogEntry};

use crate::{meta, meta::Cfg};

type Ident = (&'static str, fn(&Cfg, &ReportLogEntry) -> String);

const IDENTS: [Ident; 21] = [
    ("%ei", event_id),
    ("%en", event_name),
    ("%ef", event_file),
    ("%el", event_line),
    ("%et", event_tags),
    ("%ed", event_description),
    ("%eh", event_type_hint),
    ("%ep", event_payload),
    ("%er", raw_event_payload),
    ("%ec", event_coordinate),
    ("%eo", event_clock_offset),
    ("%pi", probe_id),
    ("%pn", probe_name),
    ("%pc", probe_clock),
    ("%pd", probe_description),
    ("%pf", probe_file),
    ("%pl", probe_line),
    ("%pt", probe_tags),
    ("%ci", component_id),
    ("%cn", component_name),
    ("%rt", receive_time),
];

pub(crate) fn format(cfg: &Cfg, row: &ReportLogEntry, fmt: &str) -> String {
    if &fmt.to_lowercase() == "syslog" {
        let pname = cfg
            .probes
            .get(&row.probe_id.get_raw())
            .map(|p| p.name.clone())
            .unwrap_or_else(|| row.probe_id.get_raw().to_string());
        let descrip = match row.data {
            LogEntryData::Event(id) => meta::get_event_meta(cfg, &row.probe_id, &id)
                .map(|e| e.description.clone())
                .unwrap_or_else(|_| String::new()),
            LogEntryData::EventWithPayload(id, _) => meta::get_event_meta(cfg, &row.probe_id, &id)
                .map(|e| e.description.clone())
                .unwrap_or_else(|_| String::new()),
            _ => String::new(),
        };
        format!(
            "PRIORITY=6 TIMESTAMP={} HOSTNAME={} MSG={}",
            row.receive_time, pname, descrip
        )
    } else {
        let mut fmt = fmt.to_string();
        for (ident, interpolator) in IDENTS.iter() {
            fmt = fmt.replace(ident, &interpolator(cfg, row));
        }
        fmt
    }
}

fn event_id(_: &Cfg, row: &ReportLogEntry) -> String {
    match row.data {
        LogEntryData::Event(id) => format!("{}", id.get_raw()),
        LogEntryData::EventWithPayload(id, _) => format!("{}", id.get_raw()),
        _ => String::new(),
    }
}

fn event_name(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .map(|e| e.name.clone())
        .unwrap_or_else(|_| String::new())
}

fn event_file(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .map(|e| e.file.clone())
        .unwrap_or_else(|_| String::new())
}

fn event_line(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .map(|e| e.line.to_string())
        .unwrap_or_else(|_| String::new())
}

fn event_tags(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .map(|e| e.tags.replace(';', ", "))
        .unwrap_or_else(|_| String::new())
}

fn event_description(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .map(|e| e.description.clone())
        .unwrap_or_else(|_| String::new())
}

fn event_type_hint(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let eid = match row.data {
        LogEntryData::Event(id) => id,
        LogEntryData::EventWithPayload(id, _) => id,
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .ok()
        .map(|e| e.type_hint.as_ref().cloned())
        .flatten()
        .unwrap_or_else(String::new)
}

fn event_payload(cfg: &Cfg, row: &ReportLogEntry) -> String {
    let (eid, pl) = match row.data {
        LogEntryData::Event(id) => (id, None),
        LogEntryData::EventWithPayload(id, pl) => (id, Some(pl)),
        _ => return String::new(),
    };
    meta::get_event_meta(cfg, &row.probe_id, &eid)
        .ok()
        .map(|e| {
            meta::parsed_payload(e.type_hint.as_ref().map(|s| s.as_ref()), pl)
                .ok()
                .flatten()
        })
        .flatten()
        .unwrap_or_else(String::new)
}

fn raw_event_payload(_: &Cfg, row: &ReportLogEntry) -> String {
    if let LogEntryData::EventWithPayload(_, pl) = row.data {
        format!("{}", pl)
    } else {
        String::new()
    }
}

fn event_coordinate(_: &Cfg, row: &ReportLogEntry) -> String {
    row.coordinate()
}

fn event_clock_offset(_: &Cfg, _: &ReportLogEntry) -> String {
    "TODO(dan@auxon.io) #278".to_string()
}

fn probe_id(_: &Cfg, row: &ReportLogEntry) -> String {
    format!("{}", row.probe_id.get_raw())
}

fn probe_name(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes.get(&row.probe_id.get_raw()) {
        Some(pmeta) => pmeta.name.clone(),
        None => format!("{}", row.probe_id.get_raw()),
    }
}

fn probe_clock(_: &Cfg, _: &ReportLogEntry) -> String {
    "TODO(dan@auxon.io) #278".to_string()
}

fn probe_description(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes.get(&row.probe_id.get_raw()) {
        Some(pmeta) => pmeta.description.clone(),
        None => String::new(),
    }
}

fn probe_file(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes.get(&row.probe_id.get_raw()) {
        Some(pmeta) => pmeta.file.clone(),
        None => String::new(),
    }
}

fn probe_line(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes.get(&row.probe_id.get_raw()) {
        Some(pmeta) => pmeta.line.to_string(),
        None => String::new(),
    }
}

fn probe_tags(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes.get(&row.probe_id.get_raw()) {
        Some(pmeta) => pmeta.tags.replace(';', ", "),
        None => String::new(),
    }
}

fn component_id(cfg: &Cfg, row: &ReportLogEntry) -> String {
    match cfg.probes_to_components.get(&row.probe_id.get_raw()) {
        Some(cid) => cid.to_string(),
        None => String::new(),
    }
}

fn component_name(cfg: &Cfg, row: &ReportLogEntry) -> String {
    if let Some(cid) = cfg.probes_to_components.get(&row.probe_id.get_raw()) {
        if let Some(cn) = cfg.component_names.get(&cid.to_string()) {
            return cn.clone();
        }
    }
    String::new()
}

fn receive_time(_: &Cfg, row: &ReportLogEntry) -> String {
    row.receive_time.to_string()
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;

    use chrono::Utc;

    use modality_probe::{EventId, NanosecondResolution, ProbeId, WallClockId};
    use modality_probe_collector_common::{
        LogEntryData, ReportLogEntry, SequenceNumber, SessionId,
    };

    use crate::{
        log,
        log::{color, Log},
        visualize::graph,
    };

    use super::*;

    const EXPECTED_GRAPH: &str = "\
|   |   |   *   event four occurred at probe four
|   |   |   |
|   +<--+   |   two merged a snapshot from three
|   |   |   |
|   |   |   *   event four occurred at probe four
|   |   |   |
|   *   |   |   event two occurred at probe two
|   |   |   |
|   |   |   *   event four occurred at probe four
|   |   |   |
+-->+   |   |   two merged a snapshot from one
|   |   |   |
*   |   |   |   event one occurred at probe one
|   |   |   |
|   *   |   |   event two occurred at probe two
|   |   |   |
*   |   |   |   event one occurred at probe one
|   |   |   |
|   +-->+   |   three merged a snapshot from two
|   |   |   |
+<--+   |   |   one merged a snapshot from two
|   |   |   |
|   *   |   |   event two occurred at probe two
|   |   |   |
|   *   |   |   event two occurred at probe two
|   |   |   |
";

    #[test]
    fn interpers() {
        let now = Utc::now();
        let cfg = graph::test::cfg();
        let row = ReportLogEntry {
            session_id: SessionId(1),
            sequence_number: SequenceNumber(1),
            sequence_index: 3,
            probe_id: ProbeId::new(4).unwrap(),
            persistent_epoch_counting: false,
            data: LogEntryData::Event(EventId::new(4).unwrap()),
            time_resolution: NanosecondResolution(0),
            wall_clock_id: WallClockId(0),
            receive_time: now,
        };

        let comp_id = cfg.component_names.iter().next().map(|(id, _)| id).unwrap();

        assert_eq!("4", &event_id(&cfg, &row));
        assert_eq!("four", event_name(&cfg, &row));
        assert_eq!("four.c", event_file(&cfg, &row));
        assert_eq!("4", event_line(&cfg, &row));
        assert_eq!("", event_tags(&cfg, &row));
        assert_eq!("four", event_description(&cfg, &row));
        assert_eq!("", event_type_hint(&cfg, &row));
        assert_eq!("", event_payload(&cfg, &row));
        assert_eq!("", raw_event_payload(&cfg, &row));
        assert_eq!("1:4:1:3", event_coordinate(&cfg, &row));
        // TODO(dan@auxon.io): #278
        // assert_eq!(event_clock_offset(&cfg, &row));
        assert_eq!("4", probe_id(&cfg, &row));
        assert_eq!("four", probe_name(&cfg, &row));
        // TODO(dan@auxon.io): #278
        // assert_eq!(probe_clock(&cfg, &row));
        assert_eq!("four", probe_description(&cfg, &row));
        assert_eq!("four.c", probe_file(&cfg, &row));
        assert_eq!("4", probe_line(&cfg, &row));
        assert_eq!("", probe_tags(&cfg, &row));
        assert_eq!(comp_id.to_string(), component_id(&cfg, &row));
        assert_eq!("component", component_name(&cfg, &row));
        assert_eq!(now.to_string(), receive_time(&cfg, &row));
    }

    #[test]
    fn graph_interp() {
        let trace = log::test::trace();
        let cfg = graph::test::cfg();
        let l = Log {
            probe: None,
            component: None,
            component_path: vec![],
            report: PathBuf::default(),
            graph: true,
            verbose: 0,
            format: Some("event %en occurred at probe %pn".to_string()),
            radius: None,
            from: None,
            no_color: true,
        };
        {
            let mut b = color::COLORIZE.write().unwrap();
            *b = false;
        }
        let (probes, clock_rows) = log::sort_probes(&cfg, &l, trace).unwrap();
        let mut out = Vec::new();
        log::print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }

    #[test]
    fn syslog_interp() {
        let now = Utc::now();
        let cfg = graph::test::cfg();
        let row = ReportLogEntry {
            session_id: SessionId(1),
            sequence_number: SequenceNumber(1),
            sequence_index: 3,
            probe_id: ProbeId::new(4).unwrap(),
            persistent_epoch_counting: false,
            data: LogEntryData::Event(EventId::new(4).unwrap()),
            time_resolution: NanosecondResolution(0),
            wall_clock_id: WallClockId(0),
            receive_time: now,
        };
        assert_eq!(
            format!("PRIORITY=6 TIMESTAMP={} HOSTNAME=four MSG=four", now),
            format(&cfg, &row, "SySlOg")
        );
    }
}
