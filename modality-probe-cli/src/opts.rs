use crate::{header_gen::HeaderGen, log::Log, manifest_gen::ManifestGen, visualize::Visualize};
use structopt::StructOpt;

#[derive(Debug, PartialEq, StructOpt)]
#[structopt(
    name = "modality-probe",
    about = "Modality probe command line interface"
)]
pub enum Opts {
    /// Generate component, event and probe manifest files from probe macro invocations
    ManifestGen(ManifestGen),

    /// Generate Rust/C header files with event/probe id constants
    HeaderGen(HeaderGen),
    /// Inspect a trace in the terminal as a log or an ASCII-based
    /// graph.
    Log(Log),
    /// Visualize a collected trace as a Graphviz dot file.
    Visualize(Visualize),
}

#[cfg(test)]
mod test {
    use std::{num::NonZeroU32, path::PathBuf};

    use pretty_assertions::assert_eq;

    use crate::{lang::Lang, manifest_gen::id_gen::NonZeroIdRange, visualize::GraphType};

    use super::*;

    #[test]
    fn parse_opts_manifest_gen() {
        assert_eq!(
            Opts::from_iter(["modality-probe", "manifest-gen", "/path",].iter()),
            Opts::ManifestGen(ManifestGen {
                lang: None,
                file_extensions: None,
                exclude_patterns: None,
                event_id_offset: None,
                probe_id_range: None,
                regen_component_id: false,
                component_name: "component".to_string(),
                output_path: PathBuf::from("component"),
                source_path: PathBuf::from("/path"),
            })
        );
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "manifest-gen",
                    "--lang",
                    "c",
                    "--event-id-offset",
                    "10",
                    "--file-extension=c",
                    "--regen-component-id",
                    "--exclude=stuff.txt",
                    "--file-extension=cpp",
                    "--probe-id-range=1..=12",
                    "--exclude=file.dep",
                    "--output-path",
                    "/out",
                    "--component-name",
                    "my-comp",
                    "/path",
                ]
                .iter()
            ),
            Opts::ManifestGen(ManifestGen {
                lang: Some(Lang::C),
                event_id_offset: Some(10),
                file_extensions: Some(vec!["c".to_string(), "cpp".to_string()]),
                exclude_patterns: Some(vec!["stuff.txt".to_string(), "file.dep".to_string()]),
                probe_id_range: Some(
                    NonZeroIdRange::new(NonZeroU32::new(1).unwrap(), NonZeroU32::new(12).unwrap())
                        .unwrap()
                ),
                component_name: "my-comp".to_string(),
                output_path: PathBuf::from("/out"),
                regen_component_id: true,
                source_path: PathBuf::from("/path"),
            })
        );
    }

    #[test]
    fn parse_opts_header_gen() {
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "header-gen",
                    "--lang",
                    "Rust",
                    "--rust-u32-types",
                    "comp",
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                lang: Lang::Rust,
                rust_u32_types: true,
                include_guard_prefix: "MODALITY_PROBE".to_string(),
                output_path: None,
                component_path: PathBuf::from("comp"),
            })
        );
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "header-gen",
                    "--lang",
                    "C",
                    "--output-path",
                    "my_dir",
                    "comp1",
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                lang: Lang::C,
                rust_u32_types: false,
                include_guard_prefix: "MODALITY_PROBE".to_string(),
                output_path: Some(PathBuf::from("my_dir")),
                component_path: PathBuf::from("comp1"),
            })
        );
    }

    #[test]
    fn parse_opts_visualize() {
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "visualize",
                    "acyclic",
                    "--component-path",
                    "component",
                    "--report",
                    "report.csv",
                ]
                .iter()
            ),
            Opts::Visualize(Visualize {
                interactions_only: false,
                include_internal_events: false,
                component_path: vec![PathBuf::from("component")],
                report: PathBuf::from("report.csv"),
                graph_type: GraphType::Acyclic,
            })
        );
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "visualize",
                    "cyclic",
                    "--interactions-only",
                    "--component-path",
                    "component",
                    "--report",
                    "report.csv",
                ]
                .iter()
            ),
            Opts::Visualize(Visualize {
                interactions_only: true,
                include_internal_events: false,
                component_path: vec![PathBuf::from("component")],
                report: PathBuf::from("report.csv"),
                graph_type: GraphType::Cyclic,
            })
        );
    }

    #[test]
    fn parse_opts_log() {
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "log",
                    "-vv",
                    "--component-path",
                    "component",
                    "--report",
                    "r.jsonl",
                    "--graph",
                    "--format",
                    "event %en occurred at probe %pn",
                ]
                .iter()
            ),
            Opts::Log(Log {
                probe: None,
                component: None,
                component_path: vec![PathBuf::from("component")],
                report: PathBuf::from("r.jsonl"),
                graph: true,
                verbose: 2,
                format: Some("event %en occurred at probe %pn".to_string()),
            })
        );
    }
}
