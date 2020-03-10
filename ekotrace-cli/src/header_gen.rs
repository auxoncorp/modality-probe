use crate::events::Event;
use crate::tracers::Tracer;
use csv;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::str::FromStr;

trait ConstGenerator {
    fn primitive_value(&self) -> u32;
    fn definition_name(&self) -> String;
    fn doc_comment(&self, lang: Lang) -> String;

    fn generate_const_definition(&self, lang: Lang) -> String {
        let definition_name = self.definition_name();
        let primitive_value = self.primitive_value();
        match lang {
            Lang::C => format!("#define {} ({}UL)", definition_name, primitive_value),
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

    fn doc_comment(&self, lang: Lang) -> String {
        match lang {
            Lang::C => {
                format!("/*\n * Tracer: {}\n * {}\n */", self.name, self.description).to_string()
            }
            Lang::Rust => {
                format!("/// Tracer: {}\n/// {}", self.name, self.description).to_string()
            }
        }
    }
}

impl ConstGenerator for Event {
    fn primitive_value(&self) -> u32 {
        self.id.0
    }

    fn definition_name(&self) -> String {
        format!("{}", self.name.to_uppercase())
    }

    fn doc_comment(&self, lang: Lang) -> String {
        match lang {
            Lang::C => format!(
                "/*\n * Trace event: {}\n * {}\n */",
                self.name, self.description
            )
            .to_string(),
            Lang::Rust => {
                format!("/// Trace event: {}\n/// {}", self.name, self.description).to_string()
            }
        }
    }
}

#[derive(Debug)]
pub struct Opt {
    pub events_csv_file: PathBuf,
    pub tracers_csv_file: PathBuf,
    pub lang: Lang,
    pub include_guard_prefix: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Lang {
    C,
    Rust,
}

#[derive(Debug)]
pub struct UnsupportedLang(String);

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

pub fn run(opt: Opt) {
    opt.validate();

    let tracers_csv_hash = file_sha256(&opt.tracers_csv_file);
    let events_csv_hash = file_sha256(&opt.events_csv_file);

    let mut tracers_reader = csv::Reader::from_reader(
        File::open(&opt.tracers_csv_file).expect("Can't open tracers csv file"),
    );

    let mut events_reader = csv::Reader::from_reader(
        File::open(&opt.events_csv_file).expect("Can't open events csv file"),
    );

    println!("/*");
    println!(" * GENERATED CODE, DO NOT EDIT");
    println!(" */");
    println!();

    if opt.lang == Lang::C {
        println!(
            "#ifndef {}_GENERATED_IDENTIFIERS_H",
            opt.include_guard_prefix
        );
        println!(
            "#define {}_GENERATED_IDENTIFIERS_H",
            opt.include_guard_prefix
        );
        println!();
        println!("#ifdef __cplusplus");
        println!("extern \"C\" {{");
        println!("#endif");
        println!();
    }

    println!("/*");
    println!(" * Tracers (csv sha256sum {})", tracers_csv_hash);
    println!(" */");

    for maybe_tracer in tracers_reader.deserialize() {
        let t: Tracer = maybe_tracer.expect("Can't deserialize tracer");

        println!();
        println!("{}", t.doc_comment(opt.lang));
        println!("{}", t.generate_const_definition(opt.lang));
    }

    println!();
    println!("/*");
    println!(" * Events (csv sha256sum {})", events_csv_hash);
    println!(" */");

    for maybe_event in events_reader.deserialize() {
        let e: Event = maybe_event.expect("Can't deserialize event");

        println!();
        println!("{}", e.doc_comment(opt.lang));
        println!("{}", e.generate_const_definition(opt.lang));
    }

    if opt.lang == Lang::C {
        println!();
        println!("#ifdef __cplusplus");
        println!("}} /* extern \"C\" */");
        println!("#endif");
        println!();
        println!(
            "#endif /* {}_GENERATED_IDENTIFIERS_H */",
            opt.include_guard_prefix
        );
        println!();
    }
}
