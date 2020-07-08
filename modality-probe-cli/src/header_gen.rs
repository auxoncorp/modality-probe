use crate::{component_dir::ComponentDir, events::Event, lang::Lang, probes::Probe};
use std::fs::File;
use std::io;
use std::path::PathBuf;
use std::str::FromStr;
use structopt::StructOpt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, StructOpt)]
pub struct HeaderGen {
    /// Component paths.
    ///
    /// All provided components will be combined into a single header file.
    #[structopt(long, required = true)]
    pub components: Vec<PathBuf>,

    /// The language to output the source in. Either `c' or `rust'.
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
            components: Vec::new(),
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
                "/*\n * Name: {}\n * Description:{}\n * Component UUID: {}\n * Tags:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                self.uuid,
                pad_nonempty(&self.tags),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Component UUID: {}\n/// Tags:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                self.uuid,
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
                "/*\n * Name: {}\n * Description:{}\n * Component UUID: {}\n * Tags:{}\n * Payload type:{}\n * Location: {}:{}\n */",
                self.name,
                pad_nonempty(&self.description),
                self.uuid,
                pad_nonempty(&self.tags),
                pad_nonempty(&self.type_hint),
                self.file,
                self.line
            ),
            Lang::Rust => format!(
                "/// Name: {}\n/// Description:{}\n/// Component UUID: {}\n/// Tags:{}\n/// Payload type:{}\n/// Location: {}:{}",
                self.name,
                pad_nonempty(&self.description),
                self.uuid,
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

pub fn generate_output<W: io::Write>(
    opt: HeaderGen,
    mut w: W,
    internal_events: Vec<u32>,
) -> Result<(), Box<dyn std::error::Error>> {
    let components: Vec<ComponentDir> = opt
        .components
        .iter()
        .flat_map(ComponentDir::collect_from_path)
        .collect();

    // Events are dup'd across logically organized
    // components that were generated from the same
    // source tree / manifest-gen scan
    let mut unique_events: Vec<Event> = components
        .iter()
        .flat_map(|comp_dir| comp_dir.events.iter())
        .cloned()
        .collect();
    unique_events.sort_by(|a, b| a.id.cmp(&b.id));
    unique_events.dedup();

    writeln!(w, "/*")?;
    writeln!(w, " * GENERATED CODE, DO NOT EDIT")?;
    for comp_dir in components.iter() {
        writeln!(w, " *")?;
        writeln!(w, " * Component:")?;
        writeln!(w, " *   Name: {}", comp_dir.component.name)?;
        writeln!(w, " *   UUID: {}", comp_dir.component.uuid)?;
        write!(w, " *   Code hash: ")?;
        match comp_dir.component.code_hash {
            Some(hash) => writeln!(w, "{}", hash)?,
            None => writeln!(w, "None")?,
        }
        write!(w, " *   Instrumentation hash: ")?;
        match comp_dir.component.instrumentation_hash {
            Some(hash) => writeln!(w, "{}", hash)?,
            None => writeln!(w, "None")?,
        }
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
    writeln!(w, " * Probes")?;
    writeln!(w, " */")?;

    for comp_dir in components.iter() {
        for probe in comp_dir.probes.iter() {
            writeln!(w)?;
            writeln!(w, "{}", probe.doc_comment(opt.lang))?;
            writeln!(w, "{}", probe.generate_const_definition(opt.lang))?;
        }
    }

    writeln!(w)?;
    writeln!(w, "/*")?;
    writeln!(w, " * Events")?;
    writeln!(w, " */")?;

    for event in unique_events.iter() {
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
    let io_out: Box<dyn io::Write> = if let Some(p) = &opt.output_path {
        Box::new(File::create(p).unwrap())
    } else {
        Box::new(io::stdout())
    };

    generate_output(opt, io_out, internal_events).expect("Can't generate output");
}
