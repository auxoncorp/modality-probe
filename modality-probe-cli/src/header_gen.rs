use crate::{events::Event, lang::Lang, tracers::Tracer};
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
        self.name.to_uppercase()
    }

    fn doc_comment(&self, lang: Lang) -> String {
        match lang {
            Lang::C => format!(
                "/*\n * Name: {}\n * Description:{}\n * Tags:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                pad_nonempty(&self.tags),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Tags:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                pad_nonempty(&self.tags),
                self.file,
                self.line
            ),
        }
    }
}

impl ConstGenerator for Event {
    fn primitive_value(&self) -> u32 {
        self.id.0
    }

    fn definition_name(&self) -> String {
        self.name.to_uppercase()
    }

    fn doc_comment(&self, lang: Lang) -> String {
        match lang {
            Lang::C => format!(
                "/*\n * Name: {}\n * Description:{}\n * Tags:{}\n * Payload type:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                pad_nonempty(&self.tags),
                pad_nonempty(&self.type_hint),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Tags:{}\n/// Payload type:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                pad_nonempty(&self.tags),
                pad_nonempty(&self.type_hint),
                self.file,
                self.line
            ),
        }
    }
}

fn pad_nonempty(s: &str) -> String {
    if !s.is_empty() {
        format!(" {}", s)
    } else {
        s.to_string()
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Opt {
    pub events_csv_file: PathBuf,
    pub tracers_csv_file: PathBuf,
    pub lang: Lang,
    pub include_guard_prefix: String,
    pub output_path: Option<PathBuf>,
}

impl Default for Opt {
    fn default() -> Self {
        Opt {
            events_csv_file: PathBuf::from("events.csv"),
            tracers_csv_file: PathBuf::from("tracers.csv"),
            lang: Lang::Rust,
            include_guard_prefix: String::from("EKOTRACE"),
            output_path: None,
        }
    }
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
            "rust" | "rs" => Ok(Lang::Rust),
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

pub fn generate_output<W: io::Write>(
    opt: Opt,
    mut w: W,
    internal_events: Vec<u32>,
) -> Result<(), Box<dyn std::error::Error>> {
    let tracers_csv_hash = file_sha256(&opt.tracers_csv_file);
    let events_csv_hash = file_sha256(&opt.events_csv_file);

    let mut tracers_reader = csv::Reader::from_reader(
        File::open(&opt.tracers_csv_file).expect("Can't open tracers csv file"),
    );

    let mut events_reader = csv::Reader::from_reader(
        File::open(&opt.events_csv_file).expect("Can't open events csv file"),
    );

    writeln!(w, "/*")?;
    writeln!(w, " * GENERATED CODE, DO NOT EDIT")?;
    writeln!(w, " */")?;
    writeln!(w)?;

    if opt.lang == Lang::C {
        writeln!(
            w,
            "#ifndef {}_GENERATED_IDENTIFIERS_H",
            opt.include_guard_prefix
        )?;
        writeln!(
            w,
            "#define {}_GENERATED_IDENTIFIERS_H",
            opt.include_guard_prefix
        )?;
        writeln!(w)?;
        writeln!(w, "#ifdef __cplusplus")?;
        writeln!(w, "extern \"C\" {{")?;
        writeln!(w, "#endif")?;
        writeln!(w)?;
    }

    writeln!(w, "/*")?;
    writeln!(w, " * Tracers (csv sha256sum {})", tracers_csv_hash)?;
    writeln!(w, " */")?;

    for maybe_tracer in tracers_reader.deserialize() {
        let t: Tracer = maybe_tracer.expect("Can't deserialize tracer");

        writeln!(w)?;
        writeln!(w, "{}", t.doc_comment(opt.lang))?;
        writeln!(w, "{}", t.generate_const_definition(opt.lang))?;
    }

    writeln!(w)?;
    writeln!(w, "/*")?;
    writeln!(w, " * Events (csv sha256sum {})", events_csv_hash)?;
    writeln!(w, " */")?;

    for maybe_event in events_reader.deserialize() {
        let e: Event = maybe_event.expect("Can't deserialize event");
        if internal_events.contains(&e.id.0) {
            continue;
        }

        writeln!(w)?;
        writeln!(w, "{}", e.doc_comment(opt.lang))?;
        writeln!(w, "{}", e.generate_const_definition(opt.lang))?;
    }

    if opt.lang == Lang::C {
        writeln!(w)?;
        writeln!(w, "#ifdef __cplusplus")?;
        writeln!(w, "}} /* extern \"C\" */")?;
        writeln!(w, "#endif")?;
        writeln!(w)?;
        writeln!(
            w,
            "#endif /* {}_GENERATED_IDENTIFIERS_H */",
            opt.include_guard_prefix
        )?;
        writeln!(w)?;
    }

    Ok(())
}

pub fn run(opt: Opt, internal_events: Vec<u32>) {
    opt.validate();

    let io_out: Box<dyn io::Write> = if let Some(p) = &opt.output_path {
        Box::new(File::create(p).unwrap())
    } else {
        Box::new(io::stdout())
    };

    generate_output(opt, io_out, internal_events).expect("Can't generate output");
}
