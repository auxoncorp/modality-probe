use structopt::StructOpt;
use std::error::Error;
use std::fs::File;
use std::io::prelude::*;
use std::net::SocketAddrV4;
use std::path::PathBuf;
use std::time::Duration;
use std::fmt;

use parse_duration::parse;

use goblin::elf::Elf;
use goblin::container::Endian;

use ekotrace_debug_collector::Config;
#[derive(Debug)]
struct OptionsError {
    details: String
}

impl OptionsError {
    fn new(msg: &str) -> Self {
        OptionsError{details: msg.to_string()}
    }
}

impl fmt::Display for OptionsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"{}",self.details)
    }
}

impl Error for OptionsError {
    fn description(&self) -> &str {
        &self.details
    }
}

#[derive(Debug, Default)]
#[derive(StructOpt)]
#[
    structopt(
        name = "ekotrace-debug-collector",
        about = "Periodically collects logs from microcontrollers over debug interfaces; outputs them to a file."
    )
]
pub struct CLIOptions {
    #[structopt(short = "s", long = "session-id", default_value = "0")]
    session_id: u32,

    #[structopt(short = "l", long = "little-endian")]
    little_endian: bool,
    #[structopt(short = "b", long = "big-endian")]
    big_endian: bool,

    #[structopt(short = "e", long = "elf", parse(from_os_str))]
    elf_path: Option<PathBuf>,
    
    #[structopt(short = "a", long = "attach")]
    attach_target: Option<String>,

    #[structopt(short = "g", long = "gdb-server")]
    gdb_addr: Option<SocketAddrV4>,

    #[structopt(short = "i", long = "interval")]
    interval: String,

    #[structopt(short = "o", long = "output-file", parse(from_os_str))]
    output_path: PathBuf,

    tracer_syms: Vec<String>
}

fn config_from_options(options: CLIOptions) -> Result<Config, Box<dyn Error>> {
    let tracer_addrs = Vec::new();
    let symbols = Vec::new();
    // Separate given tracer addresses and tracer symbols
    tracer_addrs.extend(
        options.tracer_syms.iter()
            .filter(|s| s.starts_with("0x"))
            .map(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16))
    );
    symbols.extend(
        options.tracer_syms.iter()
            .filter(|s| !s.starts_with("0x"))
    );
    let mut elf_endianness = None;
    if let Some(elf_path) = options.elf_path.as_ref() {
        let mut elf_buf = Vec::new();
        let mut elf_file = open_elf(&elf_path, &mut elf_buf)?;
        for sym in symbols {
            if let Some((sym_val, _sym_size)) = parse_symbol_info(elf_file, sym){
                tracer_addrs.push(sym_val);
            } else {
                return Err(Box::new(OptionsError::new(format!(
                    "Could not find symbol value of \"{}\" in given ELF", sym))));
            }
        }
        elf_endianness = Some(elf_file.as_ref().header.endianness());
    } else {
        if !symbols.is_empty() {
            return Err(Box::new(OptionsError::new(
                "Must specify memory locations of tracers or an ELF file to recover symbol values")));
        }
    }
    
    if (options.attach_target == None && options.gdb_addr == None) ||
        (options.attach_target != None && options.gdb_addr != None) {
        return Err(Box::new(OptionsError::new(
            "Must specify exactly one of attach target and gdb server address")));
    }

    let interval = parse(options.interval)?;
    
    Ok(ekotrace_debug_collector::Config {
        session_id: options.session_id.into(),
        big_endian: use_big_endian(&options, elf_endianness)?,
        attach_target: options.attach_target,
        gdb_addr: options.gdb_addr,
        interval: interval,
        output_path: options.output_path,
        tracer_addrs: tracer_addrs
    })
}



fn open_elf<'a>(path: &PathBuf, elf_buf: &'a mut Vec<u8>) -> Result<Box<Elf<'a>>, Box<dyn Error>> {
    let mut file = File::open(path)?;
    file.read_to_end(elf_buf)?;
    match Elf::parse(elf_buf) {
        Ok(elf) => Ok(Box::new(elf)),
        Err(err) => Err(Box::new(err)),
    }
}

fn parse_symbol_info(elf_file: &mut Elf, symbol_name: &str) -> Option<(u32, u32)> {
    let log_sym = elf_file.syms.iter().find(|sym| -> bool {
        let name_opt = elf_file.strtab.get(sym.st_name);
        if let Some(name_res) = name_opt {
            if let Ok(name) = name_res {
                return name == symbol_name;
            }
        }
        return false;
    })?;
    Some((log_sym.st_value as u32, log_sym.st_size as u32))
}

fn use_big_endian(o: &CLIOptions, elf_endianness_opt: Option<goblin::error::Result<Endian>>)
    -> Result<bool, OptionsError> 
{
    if o.little_endian && o.big_endian {
        Err(OptionsError::new("Both little-endian and big-endian were specified"))
    } else if !o.little_endian && !o.big_endian {
        if let Some(elf_endianness) = elf_endianness_opt {
            match elf_endianness {
                Ok(Endian::Little) => Ok(false),
                Ok(Endian::Big) => Ok(true),
                Err(_) => {
                    println!("Warning: Endianness could not be parsed from ELF, using little endian");
                    Ok(false)
                }
            }
        } else {
            println!("Warning: Endianness not specified, using little endian");
            Ok(false)
        }
    } else if o.little_endian {
        if let Some(elf_endianness) = elf_endianness_opt {
            if let Ok(endianness) = elf_endianness {
                if endianness == Endian::Big {
                    println!("Warning: Little endian specified, but ELF is big endian");
                }
            }
        }
        Ok(false)
    } else {
        if let Some(elf_endianness) = elf_endianness_opt {
            if let Ok(endianness) = elf_endianness {
                if endianness == Endian::Little {
                    println!("Warning: Big endian specified, but ELF is little endian");
                }
            }
        }
        Ok(false)
    }
}

fn main() {
    let opts = CLIOptions::from_args();
    
    println!("Running debug collector with configuration: {:#?}", opts);
}

