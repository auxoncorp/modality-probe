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

    let component_a_dir = output_path.join("component-a");
    let component_a_path = component_a_dir.join("Component.toml");
    let events_a_path = component_a_dir.join("events.csv");
    let probes_a_path = component_a_dir.join("probes.csv");
    fs::create_dir(&component_a_dir).unwrap();

    let component_b_dir = output_path.join("component-b");
    let component_b_path = component_b_dir.join("Component.toml");
    let events_b_path = component_b_dir.join("events.csv");
    let probes_b_path = component_b_dir.join("probes.csv");
    fs::create_dir(&component_b_dir).unwrap();

    let src_path = root_path.join("src");
    fs::create_dir(&src_path).unwrap();

    let c_src_path = src_path.join("main.c");
    let rust_src_path = src_path.join("main.rs");

    // Scope this so the files get immediately closed; this matters on windows
    {
        let mut c_src_file = File::create(&c_src_path).unwrap();
        c_src_file.write_all(C_SRC.as_bytes()).unwrap();
        c_src_file.sync_all().unwrap();

        let mut rust_src_file = File::create(&rust_src_path).unwrap();
        rust_src_file.write_all(RUST_SRC.as_bytes()).unwrap();
        rust_src_file.sync_all().unwrap();

        let mut comp_a_file = File::create(&component_a_path).unwrap();
        comp_a_file
            .write_all(COMPONENT_A_TOML_WO_HASHES.as_bytes())
            .unwrap();
        comp_a_file.sync_all().unwrap();

        let mut comp_b_file = File::create(&component_b_path).unwrap();
        comp_b_file
            .write_all(COMPONENT_B_TOML_WO_HASHES.as_bytes())
            .unwrap();
        comp_b_file.sync_all().unwrap();
    }

    // Start with a component file without hashes
    let out = run_cli(&vec![
        "manifest-gen",
        "--file-extension",
        "c",
        "--file-extension",
        "rs",
        "--output-path",
        output_path.to_str().unwrap(),
        src_path.to_str().unwrap(),
    ]);
    println!("{:?}", out);
    assert!(out.status.success());

    assert!(component_a_path.exists());
    assert!(events_a_path.exists());
    assert!(probes_a_path.exists());

    assert!(component_b_path.exists());
    assert!(events_b_path.exists());
    assert!(probes_b_path.exists());

    // Hashes should be added, UUID is stable
    let component_content = fs::read_to_string(&component_a_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_A_TOML));
    let component_content = fs::read_to_string(&component_b_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_B_TOML));

    let out = run_cli(&vec![
        "manifest-gen",
        "--file-extension",
        "c",
        "--file-extension",
        "rs",
        "--output-path",
        output_path.to_str().unwrap(),
        src_path.to_str().unwrap(),
    ]);
    assert!(out.status.success());

    // Nothing changes on successive runs
    let component_content = fs::read_to_string(&component_a_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_A_TOML));
    let component_content = fs::read_to_string(&component_b_path).unwrap();
    println!("{}", component_content);
    assert!(component_content.contains(COMPONENT_B_TOML));
}

const COMPONENT_A_TOML: &'static str = r#"name = "component-a"
uuid = "642b5374-653c-493a-84dc-64b56b52338a"
code_hash = "8f93a8c2cf361b089722a0891ab0b618e960efe952fd951449b2cc22fcd2a093"
"#;

const COMPONENT_A_TOML_WO_HASHES: &'static str = r#"name = "component-a"
uuid = "642b5374-653c-493a-84dc-64b56b52338a"
"#;

const COMPONENT_B_TOML: &'static str = r#"name = "component-b"
uuid = "fa46ca95-c6fd-4020-b6a7-4323cfa084be"
code_hash = "8f93a8c2cf361b089722a0891ab0b618e960efe952fd951449b2cc22fcd2a093"
"#;

const COMPONENT_B_TOML_WO_HASHES: &'static str = r#"name = "component-b"
uuid = "fa46ca95-c6fd-4020-b6a7-4323cfa084be"
"#;

const C_SRC: &'static str = r#"
size_t err = MODALITY_PROBE_INIT(
        &probe_storage[0],
        PROBE_STORAGE_SIZE,
        PROBE_ID_A,
        COMPONENT_A,
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

const RUST_SRC: &'static str = r#"
let probe = try_initialize_at!(
    &mut storage,
    PROBE_ID_B,
    COMPONENT_B,
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
