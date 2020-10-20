#![deny(warnings)]

use std::fs::{self, File};
use std::io::Write;

mod test_helpers;
use test_helpers::run_cli;

#[test]
fn stable_uuid() {
    let root_dir = tempfile::tempdir().unwrap();
    let root_path = root_dir.path().to_owned();

    let output_path = root_path.join("out");
    fs::create_dir(&output_path).unwrap();

    let component_path = output_path.join("Component.toml");
    let events_path = output_path.join("events.csv");
    let probes_path = output_path.join("probes.csv");

    let src_path = root_path.join("src");
    fs::create_dir(&src_path).unwrap();

    let c_src_path = src_path.join("main.c");
    let rust_src_path = src_path.join("main.rs");
    let c_excluded_src_path = src_path.join("exclude.c");

    // Scope this so the files get immediately closed; this matters on windows
    {
        let mut c_src_file = File::create(&c_src_path).unwrap();
        c_src_file.write_all(C_SRC.as_bytes()).unwrap();
        c_src_file.sync_all().unwrap();

        let mut c_exclude_src_file = File::create(&c_excluded_src_path).unwrap();
        c_exclude_src_file
            .write_all(C_EXCLUDE_SRC.as_bytes())
            .unwrap();
        c_exclude_src_file.sync_all().unwrap();

        let mut rust_src_file = File::create(&rust_src_path).unwrap();
        rust_src_file.write_all(RUST_SRC.as_bytes()).unwrap();
        rust_src_file.sync_all().unwrap();

        let mut comp_file = File::create(&component_path).unwrap();
        comp_file
            .write_all(COMPONENT_TOML_WO_HASHES.as_bytes())
            .unwrap();
        comp_file.sync_all().unwrap();
    }

    // Start with a component file without hashes
    let out = run_cli(&vec![
        "manifest-gen",
        "--exclude",
        "exclude.c",
        "--file-extension",
        "c",
        "--file-extension",
        "rs",
        "--component-name",
        "my-component",
        "--output-path",
        output_path.to_str().unwrap(),
        src_path.to_str().unwrap(),
    ]);
    println!("{:?}", out);
    assert!(out.status.success());

    assert!(component_path.exists());
    assert!(events_path.exists());
    assert!(probes_path.exists());

    // Hashes should be added, UUID is stable
    let component_content = fs::read_to_string(&component_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_TOML));

    let out = run_cli(&vec![
        "manifest-gen",
        "--exclude",
        "exclude.c",
        "--file-extension",
        "c",
        "--file-extension",
        "rs",
        "--component-name",
        "my-component",
        "--output-path",
        output_path.to_str().unwrap(),
        src_path.to_str().unwrap(),
    ]);
    assert!(out.status.success());

    // Nothing changes on successive runs
    let component_content = fs::read_to_string(&component_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_TOML));
}

const COMPONENT_TOML: &'static str = r#"name = "my-component"
id = "fa46ca95-c6fd-4020-b6a7-4323cfa084be"
code_hash = "f4d29eefe0ec8137637fdc5e586539371d9784274aa3874b9c1b06ed3f2697cc"
"#;

const COMPONENT_TOML_WO_HASHES: &'static str = r#"name = "my-component"
id = "fa46ca95-c6fd-4020-b6a7-4323cfa084be"
"#;

const C_SRC: &'static str = r#"
size_t err = MODALITY_PROBE_INIT(
        &probe_storage[0],
        PROBE_STORAGE_SIZE,
        PROBE_ID_A,
        &probe,
        MODALITY_TAGS("my-tags", "more tags"),
        "Description");
assert(err == MODALITY_PROBE_ERROR_OK);

size_t err = MODALITY_PROBE_RECORD_W_U8(
        probe,
        MY_EVENT_A,
        my_data,
        MODALITY_TAGS("tag 1", "tag 2", "tag 3"));
assert(err == MODALITY_PROBE_ERROR_OK);
"#;

const C_EXCLUDE_SRC: &'static str = "#include <stdlib.h>";

const RUST_SRC: &'static str = r#"
let probe = try_initialize_at!(
    &mut storage,
    PROBE_ID_B,
    tags!("some tag"),
    "Description"
)
.expect("Could not initialize ModalityProbe");

try_expect!(
    probe,
    MY_EVENT_B,
    true != false,
    "Description",
    tags!("a tag")
)
.expect("Could not record event");
"#;
