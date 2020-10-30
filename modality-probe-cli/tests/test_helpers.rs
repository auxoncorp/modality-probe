#![deny(warnings)]

use std::path::PathBuf;
use std::process;
use std::process::Command;

pub fn run_cli(args: &Vec<&str>) -> process::Output {
    let mut cli_command = Command::new(built_executable_path("modality-probe"));
    cli_command.env("RUST_BACKTRACE", "1").args(args);
    cli_command.output().unwrap()
}

fn get_target_dir() -> PathBuf {
    let bin = std::env::current_exe().expect("exe path");
    let mut target_dir = PathBuf::from(bin.parent().expect("bin parent"));
    while target_dir.file_name() != Some(std::ffi::OsStr::new("target")) {
        target_dir.pop();
    }
    target_dir
}

fn built_executable_path(name: &str) -> PathBuf {
    let program_path =
        get_target_dir()
            .join("debug")
            .join(format!("{}{}", name, std::env::consts::EXE_SUFFIX));

    program_path.canonicalize().expect(&format!(
        "Cannot resolve {} at {:?}",
        name,
        program_path.display()
    ))
}
