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
    use crate::{export::GraphType, lang::Lang};
    use pretty_assertions::assert_eq;
    use std::path::PathBuf;

    #[test]
    fn parse_opts_manifest_gen() {
        assert_eq!(
            Opts::from_iter(["modality-probe", "manifest-gen", "/path",].iter()),
            Opts::ManifestGen(ManifestGen {
                lang: None,
                event_id_offset: None,
                probe_id_offset: None,
                file_extensions: None,
                component_name: String::from("component"),
                output_path: PathBuf::from("component"),
                regen_component_uuid: false,
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
                    "--component-name",
                    "my-comp",
                    "--file-extension=c",
                    "--regen-component-uuid",
                    "--file-extension=cpp",
                    "--output-path",
                    "/out",
                    "/path",
                ]
                .iter()
            ),
            Opts::ManifestGen(ManifestGen {
                lang: Some(Lang::C),
                event_id_offset: Some(10),
                probe_id_offset: None,
                file_extensions: Some(vec!["c".to_string(), "cpp".to_string()]),
                component_name: String::from("my-comp"),
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
                    "events.csv",
                    "probes.csv"
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                events_csv_file: PathBuf::from("events.csv"),
                probes_csv_file: PathBuf::from("probes.csv"),
                lang: Lang::Rust,
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
                    "events.csv",
                    "probes.csv",
                    "--output-path",
                    "my_dir"
                ]
                .iter()
            ),
            Opts::HeaderGen(HeaderGen {
                events_csv_file: PathBuf::from("events.csv"),
                probes_csv_file: PathBuf::from("probes.csv"),
                lang: Lang::C,
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
