use crate::{export::Export, header_gen::HeaderGen, manifest_gen::ManifestGen};
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

    /// Export a collected event log in a well-known graph format.
    Export(Export),
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::manifest_gen::id_gen::NonZeroIdRange;
    use crate::{export::GraphType, lang::Lang};
    use core::num::NonZeroU32;
    use pretty_assertions::assert_eq;
    use std::path::PathBuf;

    #[test]
    fn parse_opts_manifest_gen() {
        assert_eq!(
            Opts::from_iter(["modality-probe", "manifest-gen", "/path",].iter()),
            Opts::ManifestGen(ManifestGen {
                lang: None,
                file_extensions: None,
                event_id_offset: None,
                probe_id_range: None,
                regen_component_uuid: false,
                output_path: PathBuf::from("components"),
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
                    "--regen-component-uuid",
                    "--file-extension=cpp",
                    "--probe-id-range=1..=12",
                    "--output-path",
                    "/out",
                    "/path",
                ]
                .iter()
            ),
            Opts::ManifestGen(ManifestGen {
                lang: Some(Lang::C),
                event_id_offset: Some(10),
                file_extensions: Some(vec!["c".to_string(), "cpp".to_string()]),
                probe_id_range: Some(
                    NonZeroIdRange::new(NonZeroU32::new(1).unwrap(), NonZeroU32::new(12).unwrap())
                        .unwrap()
                ),
                output_path: PathBuf::from("/out"),
                regen_component_uuid: true,
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
                    "--components",
                    "my-comps",
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                lang: Lang::Rust,
                components: vec![PathBuf::from("my-comps")],
                include_guard_prefix: "MODALITY_PROBE".to_string(),
                output_path: None,
            })
        );
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "header-gen",
                    "--lang",
                    "C",
                    "--components",
                    "comp1",
                    "--components",
                    "comp2",
                    "--output-path",
                    "my_dir"
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                lang: Lang::C,
                components: vec![PathBuf::from("comp1"), PathBuf::from("comp2")],
                include_guard_prefix: "MODALITY_PROBE".to_string(),
                output_path: Some(PathBuf::from("my_dir")),
            })
        );
    }

    #[test]
    fn parse_opts_export() {
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "export",
                    "acyclic",
                    "--events",
                    "events.csv",
                    "--probes",
                    "probes.csv",
                    "--report",
                    "report.csv",
                ]
                .iter()
            ),
            Opts::Export(Export {
                interactions_only: false,
                events: PathBuf::from("events.csv"),
                probes: PathBuf::from("probes.csv"),
                report: PathBuf::from("report.csv"),
                graph_type: GraphType::Acyclic,
            })
        );
        assert_eq!(
            Opts::from_iter(
                [
                    "modality-probe",
                    "export",
                    "cyclic",
                    "--interactions-only",
                    "--events",
                    "events.csv",
                    "--probes",
                    "probes.csv",
                    "--report",
                    "report.csv",
                ]
                .iter()
            ),
            Opts::Export(Export {
                interactions_only: true,
                events: PathBuf::from("events.csv"),
                probes: PathBuf::from("probes.csv"),
                report: PathBuf::from("report.csv"),
                graph_type: GraphType::Cyclic,
            })
        );
    }
}
