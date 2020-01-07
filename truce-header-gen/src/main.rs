use csv;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

#[derive(Debug, Deserialize)]
struct EventId(u32);

#[derive(Debug, Deserialize)]
struct TracerId(u32);

#[derive(Debug, Deserialize)]
struct Event {
    id: EventId,
    name: String,
    description: String,
}

#[derive(Debug, Deserialize)]
struct Tracer {
    id: TracerId,
    name: String,
    description: String,
}

#[derive(Debug, StructOpt)]
#[structopt(
    name = "truce-header-gen",
    about = "Generate C header files with event/tracer id constants."
)]
struct Opt {
    /// Events csv file
    #[structopt(parse(from_os_str))]
    events_csv_file: PathBuf,

    /// Tracers csv file
    #[structopt(parse(from_os_str))]
    tracers_csv_file: PathBuf,
}

impl Opt {
    pub fn validate(&self) {
        assert!(
            self.events_csv_file.exists(),
            "Events csv file \"{}\" does not exist",
            self.events_csv_file.display()
        );

        assert!(
            self.tracers_csv_file.exists(),
            "Tracers csv file \"{}\" does not exist",
            self.tracers_csv_file.display()
        );
    }
}

fn file_sha256(path: &Path) -> String {
    let mut file =
        File::open(path).expect(&format!("Can't open file {} for hashing", path.display()));
    let mut sha256 = Sha256::new();
    io::copy(&mut file, &mut sha256).expect(&format!("Error hashing file {}", path.display()));
    format!("{:x}", sha256.result())
}

fn main() {
    let opt = Opt::from_args();
    opt.validate();

    let tracers_csv_hash = file_sha256(&opt.tracers_csv_file);
    let events_csv_hash = file_sha256(&opt.events_csv_file);

    let mut tracers_reader = csv::Reader::from_reader(
        File::open(&opt.tracers_csv_file).expect("Can't open tracers csv file"),
    );

    let mut events_reader = csv::Reader::from_reader(
        File::open(&opt.events_csv_file).expect("Can't open events csv file"),
    );

    println!("//");
    println!("// GENERATED CODE, DO NOT EDIT");
    println!("//");
    println!("");

    println!("//");
    println!("// Tracers (csv sha256sum {})", tracers_csv_hash);
    println!("//");

    for maybe_tracer in tracers_reader.deserialize() {
        let t: Tracer = maybe_tracer.expect("Can't deserialize tracer");
        let const_name = format!("TR_{}", t.name.to_uppercase());

        println!("");
        println!("/// Tracer: {}", t.name);
        println!("/// {}", t.description);
        println!("#define {} {}", const_name, t.id.0);
    }

    println!("");
    println!("//");
    println!("// Events (csv sha256sum {})", events_csv_hash);
    println!("//");

    for maybe_event in events_reader.deserialize() {
        let e: Event = maybe_event.expect("Can't deserialize event");
        let const_name = format!("EV_{}", e.name.to_uppercase());

        println!("");
        println!("/// Trace event: {}", e.name);
        println!("/// {}", e.description);
        println!("#define {} {}", const_name, e.id.0);
    }
}
