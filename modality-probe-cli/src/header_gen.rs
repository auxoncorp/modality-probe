use crate::{
    component::Component,
    events::{Event, Events},
    exit_error,
    lang::Lang,
    probes::{Probe, Probes},
};
use sha3::{Digest, Sha3_256};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use structopt::StructOpt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, StructOpt)]
pub struct HeaderGen {
    /// The language to output the source in. Either `c' or `rust'.
    #[structopt(short, long, parse(try_from_str), default_value = "C")]
    pub lang: Lang,

    /// C header include guard prefix
    #[structopt(long, default_value = "MODALITY_PROBE")]
    pub include_guard_prefix: String,

    /// Write output to file (instead of stdout)
    #[structopt(short = "o", long, parse(from_os_str))]
    pub output_path: Option<PathBuf>,

    /// Component path
    #[structopt(parse(from_os_str))]
    pub component_path: PathBuf,
}

impl Default for HeaderGen {
    fn default() -> Self {
        HeaderGen {
            component_path: PathBuf::new(),
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
                "/*\n * Name: {}\n * Description:{}\n * Component ID: {}\n * Tags:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                self.component_id,
                pad_nonempty(&self.tags),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Component ID: {}\n/// Tags:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                self.component_id,
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
                "/*\n * Name: {}\n * Description:{}\n * Component ID: {}\n * Tags:{}\n * Payload type:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                self.component_id,
                pad_nonempty(&self.tags),
                pad_nonempty(&self.type_hint),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Component ID: {}\n/// Tags:{}\n/// Payload type:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                self.component_id,
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
        if !self.component_path.exists() {
            exit_error!(
                "manifest-gen",
                "The component path '{}' does not exist",
                self.component_path.display()
            );
        }

        let component_manifest_path = Component::component_manifest_path(&self.component_path);
        if !component_manifest_path.exists() {
            exit_error!(
                "manifest-gen",
                "The component manifest path '{}' does not exist",
                component_manifest_path.display()
            );
        }

        let probes_manifest_path = Component::probes_manifest_path(&self.component_path);
        if !probes_manifest_path.exists() {
            exit_error!(
                "manifest-gen",
                "The probes manifest path '{}' does not exist",
                probes_manifest_path.display()
            );
        }

        let events_manifest_path = Component::events_manifest_path(&self.component_path);
        if !events_manifest_path.exists() {
            exit_error!(
                "manifest-gen",
                "The events manifest path '{}' does not exist",
                events_manifest_path.display()
            );
        }
    }
}

fn file_sha256<P: AsRef<Path>>(path: P) -> String {
    let mut file = File::open(path.as_ref()).unwrap_or_else(|e| {
        exit_error!(
            "manifest-gen",
            "Can't open file {} for hashing: {}",
            path.as_ref().display(),
            e
        )
    });
    let mut sha256 = Sha3_256::new();
    io::copy(&mut file, &mut sha256).unwrap_or_else(|e| {
        exit_error!(
            "manifest-gen",
            "Error hashing file {}: {}",
            path.as_ref().display(),
            e
        )
    });
    format!("{:x}", sha256.finalize())
}

pub fn generate_output<W: io::Write>(
    opt: HeaderGen,
    mut w: W,
    internal_events: Vec<u32>,
) -> Result<(), Box<dyn std::error::Error>> {
    let component_manifest_path = Component::component_manifest_path(&opt.component_path);
    let probes_manifest_path = Component::probes_manifest_path(&opt.component_path);
    let events_manifest_path = Component::events_manifest_path(&opt.component_path);

    let probes_file_hash = file_sha256(&probes_manifest_path);
    let events_file_hash = file_sha256(&events_manifest_path);

    let component = Component::from_toml(&component_manifest_path);
    let probes = Probes::from_csv(&probes_manifest_path);
    let events = Events::from_csv(&events_manifest_path);

    writeln!(w, "/*")?;
    writeln!(w, " * GENERATED CODE, DO NOT EDIT")?;
    writeln!(w, " *")?;
    writeln!(w, " * Component:")?;
    writeln!(w, " *   Name: {}", component.name)?;
    writeln!(w, " *   ID: {}", component.id)?;
    write!(w, " *   Code hash: ")?;
    match component.code_hash {
        Some(hash) => writeln!(w, "{}", hash)?,
        None => writeln!(w, "None")?,
    }
    write!(w, " *   Instrumentation hash: ")?;
    match component.instrumentation_hash {
        Some(hash) => writeln!(w, "{}", hash)?,
        None => writeln!(w, "None")?,
    }
    writeln!(w, " */")?;

    if opt.lang == Lang::C {
        writeln!(w)?;
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
    }

    writeln!(w)?;
    writeln!(w, "/*")?;
    writeln!(w, " * Probes (sha3-256 {})", probes_file_hash)?;
    writeln!(w, " */")?;

    for probe in probes.iter() {
        writeln!(w)?;
        writeln!(w, "{}", probe.doc_comment(opt.lang))?;
        writeln!(w, "{}", probe.generate_const_definition(opt.lang))?;
    }

    writeln!(w)?;
    writeln!(w, "/*")?;
    writeln!(w, " * Events (sha3-256 {})", events_file_hash)?;
    writeln!(w, " */")?;

    for event in events.iter() {
        if internal_events.contains(&event.id.0) {
            continue;
        }

        writeln!(w)?;
        writeln!(w, "{}", event.doc_comment(opt.lang))?;
        writeln!(w, "{}", event.generate_const_definition(opt.lang))?;
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
