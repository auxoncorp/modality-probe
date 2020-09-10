#[cfg(target_family = "unix")]
use nix::{
    sys::signal::{self, Signal},
    unistd::Pid,
};
use std::{fs, io, path::Path, process::Command, thread, time::Duration};

#[test]
fn end_to_end_workflow() -> io::Result<()> {
    // This test will store artifacts (report logs, export graph, etc) in target/artifacts
    let src_dir = env!("CARGO_MANIFEST_DIR");
    let artifact_path = Path::new(src_dir).join("target").join("artifacts");
    fs::create_dir_all(&artifact_path).expect("Could not create artifacts path");

    // The report log file storing the output of modality-probe-udp-collector
    let report_log_path = artifact_path.join("report_log");

    // The exported graph of the log file
    let graph_path = artifact_path.join("graph.dot");

    let example_bin_path = Path::new(env!("CARGO_BIN_EXE_rust-example"));
    assert!(example_bin_path.exists());

    // Build modality-probe-cli
    let status = Command::new("cargo")
        .current_dir("../../")
        .args(&["build", "-p", "modality-probe-cli"])
        .status()
        .unwrap();
    assert!(status.success(), "Could not build modality-probe-cli");

    let cli = fs::canonicalize("../../target/debug/modality-probe")
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

    let udp_collector = fs::canonicalize("../../target/debug/modality-probe-udp-collector")
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

    // Start up the example application
    let mut example_app_child = Command::new(&example_bin_path)
        .spawn()
        .expect("Could not spawn rust-example application");

    println!(
        "Started the example application, process-id: {}",
        example_app_child.id()
    );

    // Run the example for a few seconds
    thread::sleep(Duration::from_secs(5));

    #[cfg(target_family = "unix")]
    signal::kill(Pid::from_raw(example_app_child.id() as _), Signal::SIGINT).unwrap();

    #[cfg(target_family = "windows")]
    example_app_child
        .kill()
        .expect("Could not kill the example application");

    let status = example_app_child
        .wait()
        .expect("Could not wait on rust-example application child");
    assert!(
        status.success(),
        "rust-example application returned a non-zero exit status"
    );

    #[cfg(target_family = "unix")]
    signal::kill(Pid::from_raw(udp_collector_child.id() as _), Signal::SIGINT).unwrap();

    #[cfg(target_family = "windows")]
    udp_collector_child
        .kill()
        .expect("Could not kill the example application");

    let status = udp_collector_child
        .wait()
        .expect("Could not wait on modality-probe-udp-collector child");
    assert!(
        status.success(),
        "modality-probe-udp-collector returned a non-zero exit status"
    );

    // Use the cli to export a graph
    let output = Command::new(&cli)
        .args(&[
            "export",
            "cyclic",
            "--components",
            "example-component",
            "--report",
            report_log_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "Could not export a graph");
    fs::write(&graph_path, output.stdout).expect("Could not write graph output");

    Ok(())
}
