use csv;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::str::FromStr;
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

trait ConstGenerator {
    fn primitive_value(&self) -> u32;
    fn definition_name(&self) -> String;

    fn generate_const_definition(&self, lang: Lang) -> String {
        let definition_name = self.definition_name();
        let primitive_value = self.primitive_value();
        match lang {
            Lang::C => format!("#define {} {}", definition_name, primitive_value),
            Lang::Rust => format!("pub const {}: u32 = {};", definition_name, primitive_value),
        }
    }
}

impl ConstGenerator for Tracer {
    fn primitive_value(&self) -> u32 {
        self.id.0
    }

    fn definition_name(&self) -> String {
        format!("{}", self.name.to_uppercase())
    }
}

impl ConstGenerator for Event {
    fn primitive_value(&self) -> u32 {
        self.id.0
    }

    fn definition_name(&self) -> String {
        format!("{}", self.name.to_uppercase())
    }
}

#[derive(Debug, StructOpt)]
#[structopt(
    name = "ekotrace-header-gen",
    about = "Generate C header files with event/tracer id constants."
)]
struct Opt {
    /// Events csv file
    #[structopt(parse(from_os_str))]
    events_csv_file: PathBuf,

    /// Tracers csv file
    #[structopt(parse(from_os_str))]
    tracers_csv_file: PathBuf,

    #[structopt(short, long, parse(try_from_str), default_value = "C")]
    lang: Lang,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Lang {
    C,
    Rust,
}

#[derive(Debug)]
struct UnsupportedLang(String);

impl ToString for UnsupportedLang {
    fn to_string(&self) -> String {
        format!("{:?}", self)
    }
}

impl FromStr for Lang {
    type Err = UnsupportedLang;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_lowercase();
        match s.trim() {
            "c" => Ok(Lang::C),
            "rust" => Ok(Lang::Rust),
            "rs" => Ok(Lang::Rust),
            _ => Err(UnsupportedLang(s)),
        }
    }
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
    let mut file = File::open(path)
        .unwrap_or_else(|e| panic!("Can't open file {} for hashing: {}", path.display(), e));
    let mut sha256 = Sha256::new();
    io::copy(&mut file, &mut sha256)
        .unwrap_or_else(|e| panic!("Error hashing file {}: {}", path.display(), e));
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
    println!();

    println!("//");
    println!("// Tracers (csv sha256sum {})", tracers_csv_hash);
    println!("//");

    for maybe_tracer in tracers_reader.deserialize() {
        let t: Tracer = maybe_tracer.expect("Can't deserialize tracer");

        println!();
        println!("/// Tracer: {}", t.name);
        println!("/// {}", t.description);
        println!("{}", t.generate_const_definition(opt.lang));
    }

    println!();
    println!("//");
    println!("// Events (csv sha256sum {})", events_csv_hash);
    println!("//");

    for maybe_event in events_reader.deserialize() {
        let e: Event = maybe_event.expect("Can't deserialize event");

        println!();
        println!("/// Trace event: {}", e.name);
        println!("/// {}", e.description);
        println!("{}", e.generate_const_definition(opt.lang));
    }
}
