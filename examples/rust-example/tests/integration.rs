#![deny(warnings)]

#[cfg(target_family = "unix")]
use nix::{
    sys::signal::{self, Signal},
    unistd::Pid,
};
use std::{
    fs, io,
    path::{Path, PathBuf},
    process::Command,
    thread,
    time::Duration,
};

#[test]
fn end_to_end_workflow() -> io::Result<()> {
    // This test will store artifacts (report logs, export graph, etc) in target/artifacts
    let src_dir = env!("CARGO_MANIFEST_DIR");
    let artifact_path = Path::new(src_dir).join("target").join("artifacts");
    if artifact_path.exists() {
        fs::remove_dir_all(&artifact_path).expect("Could not clean artifact path");
    }
    fs::create_dir_all(&artifact_path).expect("Could not create artifacts path");

    // The report log file storing the output of modality-probe-udp-collector
    let report_log_path = artifact_path.join("report_log.jsonl");

    // The exported graph of the log file
    let cyclic_graph_path = artifact_path.join("cyclic_graph.dot");
    let acyclic_graph_path = artifact_path.join("acyclic_graph.dot");

    let example_bin_path = Path::new(env!("CARGO_BIN_EXE_rust-example"));
    assert!(example_bin_path.exists());

    // Build modality-probe-cli
    let status = Command::new("cargo")
        .current_dir("../../")
        .args(&["build", "-p", "modality-probe-cli"])
        .status()
        .unwrap();
    assert!(status.success(), "Could not build modality-probe-cli");

    let cli = executable_path("../../target/debug/modality-probe")
        .expect("Could not find modality-probe binary");

    // Build modality-probe-udp-collector
    let status = Command::new("cargo")
        .current_dir("../../")
        .args(&["build", "-p", "modality-probe-udp-collector"])
        .status()
        .unwrap();
    assert!(
        status.success(),
        "Could not build modality-probe-udp-collector"
    );

    let udp_collector = executable_path("../../target/debug/modality-probe-udp-collector")
        .expect("Could not find modality-probe-udp-collector binary");

    // Start up the UDP collector
    let mut udp_collector_child = Command::new(&udp_collector)
        .args(&[
            "--port",
            "2718",
            "--session-id",
            "1",
            "--output-file",
            report_log_path.to_str().unwrap(),
        ])
        .spawn()
        .expect("Could not spawn modality-probe-udp-collector");

    println!(
        "Started the UDP collector, process-id: {}",
        udp_collector_child.id()
    );

    thread::sleep(Duration::from_secs(1));

    // Run the example application
    let status = Command::new(&example_bin_path).status().unwrap();
    assert!(status.success(), "Could not run rust-example application");

    thread::sleep(Duration::from_secs(1));

    #[cfg(target_family = "unix")]
    signal::kill(Pid::from_raw(udp_collector_child.id() as _), Signal::SIGINT).unwrap();

    #[cfg(target_family = "windows")]
    udp_collector_child
        .kill()
        .expect("Could not kill the example application");

    #[cfg(target_family = "unix")]
    {
        let status = udp_collector_child
            .wait()
            .expect("Could not wait on modality-probe-udp-collector child");
        assert!(
            status.success(),
            "modality-probe-udp-collector returned a non-zero exit status"
        );
    }

    #[cfg(target_family = "windows")]
    let _status = udp_collector_child
        .wait()
        .expect("Could not wait on modality-probe-udp-collector child");

    // Use the cli to export a graph
    let output = Command::new(&cli)
        .args(&[
            "export",
            "cyclic",
            "--component-path",
            "example-component",
            "--report",
            report_log_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "Could not export cyclic graph");
    fs::write(&cyclic_graph_path, output.stdout).expect("Could not write cyclic graph output");
    let metadata = fs::metadata(&cyclic_graph_path).expect("Could not read cyclic graph output");
    assert_ne!(metadata.len(), 0);

    let output = Command::new(&cli)
        .args(&[
            "export",
            "acyclic",
            "--component-path",
            "example-component",
            "--report",
            report_log_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "Could not export acyclic graph");
    fs::write(&acyclic_graph_path, output.stdout).expect("Could not write acyclic graph output");
    let metadata = fs::metadata(&acyclic_graph_path).expect("Could not read acyclic graph output");
    assert_ne!(metadata.len(), 0);

    Ok(())
}

fn executable_path(path: &str) -> Result<PathBuf, ()> {
    let p = Path::new(&format!("{}{}", path, std::env::consts::EXE_SUFFIX)).to_path_buf();
    if p.exists() {
        Ok(p)
    } else {
        Err(())
    }
}
