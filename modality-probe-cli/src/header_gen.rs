use crate::{events::Event, lang::Lang, probes::Probe};
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use structopt::StructOpt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, StructOpt)]
pub struct HeaderGen {
    /// Events csv file
    #[structopt(parse(from_os_str))]
    pub events_csv_file: PathBuf,

    /// Probes csv file
    #[structopt(parse(from_os_str))]
    pub probes_csv_file: PathBuf,

    #[structopt(short, long, parse(try_from_str), default_value = "C")]
    pub lang: Lang,

    /// C header include guard prefix
    #[structopt(long, default_value = "MODALITY_PROBE")]
    pub include_guard_prefix: String,

    /// Write output to file (instead of stdout)
    #[structopt(short = "o", long, parse(from_os_str))]
    pub output_path: Option<PathBuf>,
}

impl Default for HeaderGen {
    fn default() -> Self {
        HeaderGen {
            events_csv_file: PathBuf::from("events.csv"),
            probes_csv_file: PathBuf::from("probes.csv"),
            lang: Lang::Rust,
            include_guard_prefix: String::from("MODALITY_PROBE"),
            output_path: None,
        }
    }
}

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

impl ConstGenerator for Probe {
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

impl HeaderGen {
    pub fn validate(&self) {
        assert!(
            self.events_csv_file.exists(),
            "Events csv file \"{}\" does not exist",
            self.events_csv_file.display()
        );

        assert!(
            self.probes_csv_file.exists(),
            "Probes csv file \"{}\" does not exist",
            self.probes_csv_file.display()
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
    opt: HeaderGen,
    mut w: W,
    internal_events: Vec<u32>,
) -> Result<(), Box<dyn std::error::Error>> {
    let probes_csv_hash = file_sha256(&opt.probes_csv_file);
    let events_csv_hash = file_sha256(&opt.events_csv_file);

    let mut probes_reader = csv::Reader::from_reader(
        File::open(&opt.probes_csv_file).expect("Can't open probes csv file"),
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
    writeln!(w, " * Probes (csv sha256sum {})", probes_csv_hash)?;
    writeln!(w, " */")?;

    for maybe_probe in probes_reader.deserialize() {
        let t: Probe = maybe_probe.expect("Can't deserialize probe");

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

pub fn run(opt: HeaderGen, internal_events: Vec<u32>) {
    opt.validate();

    let io_out: Box<dyn io::Write> = if let Some(p) = &opt.output_path {
        Box::new(File::create(p).unwrap())
    } else {
        Box::new(io::stdout())
    };

    generate_output(opt, io_out, internal_events).expect("Can't generate output");
}
