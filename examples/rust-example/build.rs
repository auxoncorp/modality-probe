#![deny(warnings)]

use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn main() {
    // Build modality-probe-cli
    let status = Command::new("cargo")
        .current_dir("../../")
        .args(&["build", "-p", "modality-probe-cli"])
        .status()
        .unwrap();
    assert!(status.success(), "Could not build modality-probe-cli");

    let cli = executable_path("../../target/debug/modality-probe")
        .expect("Could not find modality-probe binary");

    // Use the cli to generate component manifests
    let status = Command::new(&cli)
        .args(&[
            "manifest-gen",
            "--lang",
            "rust",
            "--file-extension",
            "rs",
            "--component-name",
            "example-component",
            "--output-path",
            "example-component",
            ".",
        ])
        .status()
        .unwrap();
    assert!(status.success(), "Could not generate component manifests");

    // Use the cli to generate Rust definitions from the component manifests
    let status = Command::new(&cli)
        .args(&[
            "header-gen",
            "--lang",
            "rust",
            "--output-path",
            "src/component_definitions.rs",
            "example-component",
        ])
        .status()
        .unwrap();
    assert!(status.success(), "Could not generate component definitions");

    // Re-run this build script if source changes
    println!("cargo:rerun-if-changed=src/main.rs");
}

fn executable_path(path: &str) -> Result<PathBuf, ()> {
    let p = Path::new(&format!("{}{}", path, std::env::consts::EXE_SUFFIX)).to_path_buf();
    if p.exists() {
        Ok(p)
    } else {
        Err(())
    }
}
