use rust_lcm_codegen::generate;
use std::env;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=schemas");
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=build.rs");
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let output_rust_path = &out_dir.join("log_reporting.rs");
    let input_lcm_file_path = "../truce/schemas/log_reporting.lcm";
    generate(vec![input_lcm_file_path], output_rust_path);

    let mut out_file = File::open(output_rust_path).expect("open out file");
    let mut out_file_content = String::new();
    out_file
        .read_to_string(&mut out_file_content)
        .expect("read out file");
}
