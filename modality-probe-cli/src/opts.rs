use crate::{export::Export, header_gen::HeaderGen, manifest_gen::ManifestGen};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "modality-probe",
    about = "Modality probe command line interface"
)]
pub enum Opts {
    /// Generate event and probe id manifest files from probe macro invocations
    ManifestGen(ManifestGen),

    /// Generate Rust/C header files with event/probe id constants
    HeaderGen(HeaderGen),

    /// Export a collected event log in a well-known graph format.
    Export(Export),
}
