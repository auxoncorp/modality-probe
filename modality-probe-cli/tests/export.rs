#![deny(warnings)]

#[test]
#[cfg(all(
    target_os = "linux",
    target_endian = "little",
    target_pointer_width = "64"
))]
fn visualize_cli_produces_a_reasonable_dot_file() {
    use std::{
        path::PathBuf,
        process::{Command, Stdio},
    };
    let run = |args: &[&str]| {
        let cmd_path = PathBuf::from(env!("CARGO_BIN_EXE_modality-probe"));
        let mut out = Command::new(&cmd_path)
            .args(args)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        assert!(out.wait().unwrap().success());

        let dot = Command::new("dot")
            .stdin(out.stdout.unwrap())
            .args(&["-T", "svg"])
            .output()
            .unwrap();
        assert!(dot.status.success(), "{:#?}", dot)
    };

    let mut comp_path = PathBuf::new();
    comp_path.push("tests");
    comp_path.push("fixtures");
    comp_path.push("test-component");

    let mut log_path = PathBuf::new();
    log_path.push("tests");
    log_path.push("fixtures");
    log_path.push("test-log.jsonl");

    run(&[
        "visualize",
        "acyclic",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "cyclic",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "acyclic",
        "--interactions-only",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "cyclic",
        "--interactions-only",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);

    comp_path.pop();
    comp_path.push("test-component-empty");

    run(&[
        "visualize",
        "acyclic",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "cyclic",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "acyclic",
        "--interactions-only",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
    run(&[
        "visualize",
        "cyclic",
        "--interactions-only",
        "-c",
        &comp_path.display().to_string(),
        "-r",
        &log_path.display().to_string(),
    ]);
}
