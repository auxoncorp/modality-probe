use modality_probe::{EventId, ProbeId};

use crate::{meta, meta::MetaMeter};

type Ident = (&'static str, fn(&dyn MetaMeter, &Context) -> String);

const IDENTS: [Ident; 18] = [
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
    ("%pi", probe_id),
    ("%pn", probe_name),
    ("%pd", probe_description),
    ("%pf", probe_file),
    ("%pl", probe_line),
    ("%pt", probe_tags),
    ("%ci", component_id),
    ("%cn", component_name),
];

pub struct Context {
    pub probe_id: ProbeId,
    pub event_id: EventId,
    pub user_coordinate: String,
    pub payload: Option<u32>,
}

pub fn format(mm: &dyn MetaMeter, ctx: Context, fmt: &str) -> String {
    if &fmt.to_lowercase() == "syslog" {
        let pname = mm
            .probe_name(&ctx.probe_id)
            .unwrap_or_else(|| ctx.probe_id.get_raw().to_string());
        let descrip = mm
            .event_description(&ctx.probe_id, &ctx.event_id)
            .unwrap_or_else(String::new);
        // TODO(dan@auxon.io): figure out what to do with recv time.
        format!("PRIORITY=6 HOSTNAME={} MSG={}", pname, descrip)
    } else {
        let mut fmt = fmt.to_string();
        for (ident, interpolator) in IDENTS.iter() {
            fmt = fmt.replace(ident, &interpolator(mm, &ctx));
        }
        fmt
    }
}

fn event_id(_: &dyn MetaMeter, ctx: &Context) -> String {
    format!("{}", ctx.event_id.get_raw())
}

fn event_name(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_name(&ctx.probe_id, &ctx.event_id)
        .unwrap_or_else(String::new)
}

fn event_file(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_file(&ctx.probe_id, &ctx.event_id)
        .unwrap_or_else(String::new)
}

fn event_line(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_line(&ctx.probe_id, &ctx.event_id)
        .unwrap_or_else(String::new)
}

fn event_tags(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_tags(&ctx.probe_id, &ctx.event_id)
        .map(|tags| tags.join(", "))
        .unwrap_or_else(String::new)
}

fn event_description(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_description(&ctx.probe_id, &ctx.event_id)
        .unwrap_or_else(String::new)
}

fn event_type_hint(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_type_hint(&ctx.probe_id, &ctx.event_id)
        .unwrap_or_else(String::new)
}

fn event_payload(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.event_type_hint(&ctx.probe_id, &ctx.event_id)
        .map(|th| meta::parsed_payload(Some(&th), ctx.payload).ok().flatten())
        .flatten()
        .unwrap_or_else(String::new)
}

fn raw_event_payload(_: &dyn MetaMeter, ctx: &Context) -> String {
    ctx.payload
        .map(|pl| pl.to_string())
        .unwrap_or_else(String::new)
}

fn event_coordinate(_: &dyn MetaMeter, ctx: &Context) -> String {
    ctx.user_coordinate.clone()
}

fn probe_id(_: &dyn MetaMeter, ctx: &Context) -> String {
    ctx.probe_id.get_raw().to_string()
}

fn probe_name(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_name(&ctx.probe_id).unwrap_or_else(String::new)
}

fn probe_description(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_description(&ctx.probe_id)
        .unwrap_or_else(String::new)
}

fn probe_file(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_file(&ctx.probe_id).unwrap_or_else(String::new)
}

fn probe_line(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_line(&ctx.probe_id).unwrap_or_else(String::new)
}

fn probe_tags(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_tags(&ctx.probe_id)
        .map(|tags| tags.join(", "))
        .unwrap_or_else(String::new)
}

fn component_id(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_component_id(&ctx.probe_id)
        .map(|cid| cid.to_string())
        .unwrap_or_else(String::new)
}

fn component_name(mm: &dyn MetaMeter, ctx: &Context) -> String {
    mm.probe_component_name(&ctx.probe_id)
        .unwrap_or_else(String::new)
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;

    use modality_probe::{EventId, ProbeId};

    use crate::{
        log,
        log::{color, Log},
        visualize::graph,
    };

    use super::*;

    const EXPECTED_GRAPH: &str = "\
║  ║  ║  *  event four occurred at probe four
║  ║  ║  ║
║  ╔«═╝  ║  two merged a snapshot from three
║  ║  ║  ║
║  ║  ║  *  event four occurred at probe four
║  ║  ║  ║
║  *  ║  ║  event two occurred at probe two
║  ║  ║  ║
║  ║  ║  *  event four occurred at probe four
║  ║  ║  ║
╚═»╗  ║  ║  two merged a snapshot from one
║  ║  ║  ║
*  ║  ║  ║  event one occurred at probe one
║  ║  ║  ║
║  *  ║  ║  event two occurred at probe two
║  ║  ║  ║
*  ║  ║  ║  event one occurred at probe one
║  ║  ║  ║
║  ╚═»╗  ║  three merged a snapshot from two
║  ║  ║  ║
╔«═╝  ║  ║  one merged a snapshot from two
║  ║  ║  ║
║  *  ║  ║  event two occurred at probe two
║  ║  ║  ║
║  *  ║  ║  event two occurred at probe two
║  ║  ║  ║
";

    #[test]
    fn interpers() {
        let cfg = graph::test::cfg();

        let comp_id = cfg.component_names.iter().next().map(|(id, _)| id).unwrap();

        let context = Context {
            probe_id: ProbeId::new(4).unwrap(),
            event_id: EventId::new(4).unwrap(),
            payload: None,
            user_coordinate: "1:4:65537:1:3".to_string(),
        };

        assert_eq!("4", &event_id(&cfg, &context));
        assert_eq!("four", event_name(&cfg, &context));
        assert_eq!("four.c", event_file(&cfg, &context));
        assert_eq!("4", event_line(&cfg, &context));
        assert_eq!("", event_tags(&cfg, &context));
        assert_eq!("four", event_description(&cfg, &context));
        assert_eq!("", event_type_hint(&cfg, &context));
        assert_eq!("", event_payload(&cfg, &context));
        assert_eq!("", raw_event_payload(&cfg, &context));
        assert_eq!("1:4:65537:1:3", event_coordinate(&cfg, &context));
        // TODO(dan@auxon.io): #278
        // assert_eq!(event_clock_offset(&cfg, &context));
        assert_eq!("4", probe_id(&cfg, &context));
        assert_eq!("four", probe_name(&cfg, &context));
        // TODO(dan@auxon.io): #278
        // assert_eq!(probe_clock(&cfg, &context));
        assert_eq!("four", probe_description(&cfg, &context));
        assert_eq!("four.c", probe_file(&cfg, &context));
        assert_eq!("4", probe_line(&cfg, &context));
        assert_eq!("", probe_tags(&cfg, &context));
        assert_eq!(comp_id.to_string(), component_id(&cfg, &context));
        assert_eq!("component", component_name(&cfg, &context));
    }

    #[test]
    fn graph_interp() {
        let trace = log::graph::test::trace();
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
        log::graph::print_as_graph(probes, clock_rows, &cfg, &l, &mut out).unwrap();
        assert_eq!(EXPECTED_GRAPH, std::str::from_utf8(&out).unwrap());
    }

    #[test]
    fn syslog_interp() {
        let cfg = graph::test::cfg();
        let context = Context {
            probe_id: ProbeId::new(4).unwrap(),
            event_id: EventId::new(4).unwrap(),
            payload: None,
            user_coordinate: "1:4:65537:1:3".to_string(),
        };
        assert_eq!(
            format!("PRIORITY=6 HOSTNAME=four MSG=four"),
            format(&cfg, context, "SySlOg")
        );
    }
}
