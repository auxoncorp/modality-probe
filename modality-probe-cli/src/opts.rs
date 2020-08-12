use crate::{header_gen::HeaderGen, manifest_gen::ManifestGen};
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
    // /// Export a collected event log in a well-known graph format.
    // Export(Export),
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lang::Lang;
    use crate::manifest_gen::id_gen::NonZeroIdRange;
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
                    "--file-extension=cpp",
                    "--probe-id-range=1..=12",
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
            Opts::from_iter(["modality-probe", "header-gen", "--lang", "Rust", "comp",].iter()),
            Opts::HeaderGen(HeaderGen {
                lang: Lang::Rust,
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
                include_guard_prefix: "MODALITY_PROBE".to_string(),
                output_path: Some(PathBuf::from("my_dir")),
                component_path: PathBuf::from("comp1"),
            })
        );
    }

    // #[test]
    // fn parse_opts_export() {
    //     assert_eq!(
    //         Opts::from_iter(
    //             [
    //                 "modality-probe",
    //                 "export",
    //                 "acyclic",
    //                 "--components",
    //                 "component",
    //                 "--report",
    //                 "report.csv",
    //             ]
    //             .iter()
    //         ),
    //         Opts::Export(Export {
    //             interactions_only: false,
    //             components: vec![PathBuf::from("component")],
    //             report: PathBuf::from("report.csv"),
    //             graph_type: GraphType::Acyclic,
    //         })
    //     );
    //     assert_eq!(
    //         Opts::from_iter(
    //             [
    //                 "modality-probe",
    //                 "export",
    //                 "cyclic",
    //                 "--interactions-only",
    //                 "--components",
    //                 "component",
    //                 "--report",
    //                 "report.csv",
    //             ]
    //             .iter()
    //         ),
    //         Opts::Export(Export {
    //             interactions_only: true,
    //             components: vec![PathBuf::from("component")],
    //             report: PathBuf::from("report.csv"),
    //             graph_type: GraphType::Cyclic,
    //         })
    //     );
    // }
}
