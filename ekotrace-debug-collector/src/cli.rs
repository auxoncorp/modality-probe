use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::net::SocketAddrV4;
use std::path::PathBuf;

use parse_duration::parse;
use structopt::StructOpt;

use goblin::container::Endian;
use goblin::elf::Elf;

use ekotrace_debug_collector::Config;

/// Error in options processing
#[derive(Debug)]
struct OptionsError {
    details: String,
}

impl OptionsError {
    fn new(msg: &str) -> Self {
        OptionsError {
            details: msg.to_string(),
        }
    }
}

impl fmt::Display for OptionsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl Error for OptionsError {
    fn description(&self) -> &str {
        &self.details
    }
}

#[derive(Debug, Default, StructOpt)]
#[structopt(
    name = "ekotrace-debug-collector",
    about = "Periodically collects logs from microcontrollers over debug interfaces; outputs them to a file."
)]
pub struct CLIOptions {
    /// Session id to associate with the collected trace data
    #[structopt(short = "s", long = "session-id", default_value = "0")]
    session_id: u32,

    /// Specifies little endian architecture of target system
    #[structopt(short = "l", long = "little-endian")]
    little_endian: bool,
    /// Specifies big endian architecture of target system
    #[structopt(short = "b", long = "big-endian")]
    big_endian: bool,

    /// Path of ELF file for endianness and symbol resolution
    #[structopt(short = "e", long = "elf", parse(from_os_str))]
    elf_path: Option<PathBuf>,

    /// Chip type of target system to attach to
    #[structopt(short = "a", long = "attach")]
    attach_target: Option<String>,

    /// Address of gdb server to connect to
    #[structopt(short = "g", long = "gdb-server")]
    gdb_addr: Option<SocketAddrV4>,

    /// Interval between log collections
    #[structopt(short = "i", long = "interval")]
    interval: String,

    /// Output file location
    #[structopt(short = "o", long = "output-file", parse(from_os_str))]
    output_path: PathBuf,

    /// Symbols and/or addresses of tracer references
    tracer_syms: Vec<String>,
}

/// Turn CLI options into configuration for the collector
pub(crate) fn config_from_options(options: CLIOptions) -> Result<Config, Box<dyn Error>> {
    let mut tracer_addrs = Vec::new();
    let mut symbols = Vec::new();
    // Separate tracer addresses and tracer symbols
    for addr_str in options.tracer_syms.iter().filter(|s| s.starts_with("0x")) {
        let addr = u32::from_str_radix(addr_str.trim_start_matches("0x"), 16)?;
        tracer_addrs.push(addr);
    }
    symbols.extend(options.tracer_syms.iter().filter(|s| !s.starts_with("0x")));
    let mut elf_endianness = None;
    if let Some(elf_path) = options.elf_path.as_ref() {
        let mut elf_buf = Vec::new();
        let elf_file = open_elf(&elf_path, &mut elf_buf)?;
        // Resolve symbol values
        for sym in symbols {
            if let Some((sym_val, _sym_size)) = parse_symbol_info(&elf_file, sym) {
                tracer_addrs.push(sym_val);
            } else {
                return Err(Box::new(OptionsError::new(&format!(
                    "Could not find symbol value of \"{}\" in given ELF",
                    sym
                ))));
            }
        }
        elf_endianness = Some(elf_file.as_ref().header.endianness());
    } else if !symbols.is_empty() {
        return Err(Box::new(OptionsError::new(
            "Must specify memory locations of tracers or an ELF file to recover symbol values",
        )));
    }

    // Check that one of attach target and gdb server specified
    if (options.attach_target == None && options.gdb_addr == None)
        || (options.attach_target != None && options.gdb_addr != None)
    {
        return Err(Box::new(OptionsError::new(
            "Must specify exactly one of attach target and gdb server address",
        )));
    }

    let interval = parse(&options.interval)?;

    Ok(ekotrace_debug_collector::Config {
        session_id: options.session_id.into(),
        big_endian: should_use_big_endian(&options, elf_endianness)?,
        attach_target: options.attach_target,
        gdb_addr: options.gdb_addr,
        interval,
        output_path: options.output_path,
        tracer_addrs,
    })
}

/// Open elf file for parsing
fn open_elf<'a>(path: &PathBuf, elf_buf: &'a mut Vec<u8>) -> Result<Box<Elf<'a>>, Box<dyn Error>> {
    let mut file = File::open(path)?;
    file.read_to_end(elf_buf)?;
    match Elf::parse(elf_buf) {
        Ok(elf) => Ok(Box::new(elf)),
        Err(err) => Err(Box::new(err)),
    }
}

/// Get value and size of given symbol, or None if symbol cannot be found
fn parse_symbol_info(elf_file: &Elf, symbol_name: &str) -> Option<(u32, u32)> {
    let log_sym = elf_file.syms.iter().find(|sym| -> bool {
        let name_opt = elf_file.strtab.get(sym.st_name);
        if let Some(name_res) = name_opt {
            if let Ok(name) = name_res {
                return name == symbol_name;
            }
        }
        false
    })?;
    Some((log_sym.st_value as u32, log_sym.st_size as u32))
}

/// Return whether or not big endian should be used based on specified endianness
/// and ELF endianness
fn should_use_big_endian(
    o: &CLIOptions,
    elf_endianness_opt: Option<goblin::error::Result<Endian>>,
) -> Result<bool, OptionsError> {
    if o.little_endian && o.big_endian {
        Err(OptionsError::new(
            "Both little-endian and big-endian were specified",
        ))
    } else if !o.little_endian && !o.big_endian {
        // Imply endianness from ELF
        if let Some(elf_endianness) = elf_endianness_opt {
            match elf_endianness {
                Ok(Endian::Little) => Ok(false),
                Ok(Endian::Big) => Ok(true),
                Err(_) => {
                    // Default to little endian with warning
                    println!(
                        "Warning: Endianness could not be parsed from ELF, using little endian"
                    );
                    Ok(false)
                }
            }
        } else {
            // Default to little endian with warning
            println!("Warning: Endianness not specified, using little endian");
            Ok(false)
        }
    } else if o.little_endian {
        if let Some(elf_endianness) = elf_endianness_opt {
            if let Ok(endianness) = elf_endianness {
                if endianness == Endian::Big {
                    println!("Warning: Little endian specified, but ELF is big endian. Using little endian.");
                }
            }
        }
        Ok(false)
    } else {
        if let Some(elf_endianness) = elf_endianness_opt {
            if let Ok(endianness) = elf_endianness {
                if endianness == Endian::Little {
                    println!("Warning: Big endian specified, but ELF is little endian. Using big endian.");
                }
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::canonicalize;
    use std::process::Command;
    use std::str::FromStr;
    use std::time::Duration;

    fn compile_symbol_example() {
        Command::new("cargo")
            .arg("build")
            .current_dir(canonicalize("./tests/symbols-example").unwrap())
            .output()
            .unwrap();
    }

    fn options_from_str(input: &str) -> CLIOptions {
        CLIOptions::from_iter(input.split(" "))
    }

    /// Test basic parsing
    #[test]
    fn test_basic() {
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                0x100"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x100]
            }
        )
    }

    /// Specify gdb server instead of attach target
    #[test]
    fn specify_gdb_server() {
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --little-endian \
                --gdb-server 127.0.0.1:3000 \
                --interval 1s \
                --output-file ./out \
                0x100"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: None,
                gdb_addr: Some(SocketAddrV4::from_str("127.0.0.1:3000").unwrap()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x100]
            }
        )
    }

    /// Should error if both attach target and gdb server specified
    #[test]
    fn error_on_multiple_targets() {
        if let Ok(_) = config_from_options(options_from_str(
            "ekotrace-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --gdb-server 127.0.0.1:3000 \
            --interval 1s \
            --output-file ./out \
            0x100",
        )) {
            panic!("No error when both gdb server and attach target specified")
        }
    }

    /// Should error if neither attach target nor gdb server specified
    #[test]
    fn error_on_no_target() {
        if let Ok(_) = config_from_options(options_from_str(
            "ekotrace-debug-collector \
            --session-id 0 \
            --little-endian \
            --interval 1s \
            --output-file ./out \
            0x100",
        )) {
            panic!("No error when neither gdb server or attach target specified")
        }
    }

    /// Should error if given ELF path does not exist
    #[test]
    fn error_elf_dne() {
        if let Ok(_) = config_from_options(options_from_str(
            "ekotrace-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --elf ./nonexistent
            --interval 1s \
            --output-file ./out \
            0x100",
        )) {
            panic!("No error when non-existent")
        }
    }

    /// Should error if given ELF path is not valid ELF file
    #[test]
    fn error_elf_invalid() {
        if let Ok(_) = config_from_options(options_from_str(
            "ekotrace-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --elf ./Cargo.toml
            --interval 1s \
            --output-file ./out \
            0x100",
        )) {
            panic!("No error when invalid elf specified")
        }
    }

    /// Symbol value parsing for little endian ELF
    #[test]
    fn symbol_parsing_le() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf \
                ./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example \
                v1 v2 v3"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x20000000, 0x20000004, 0x20000008]
            }
        )
    }

    /// Input both symbols and addresses
    #[test]
    fn sym_addr_mix() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf \
                ./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example \
                0x1 v1 v2 0x10 v3 0x100"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1, 0x10, 0x100, 0x20000000, 0x20000004, 0x20000008]
            }
        )
    }

    /// Should error if both big and little endian specified
    #[test]
    fn error_specify_both_endianness() {
        if let Ok(_) = config_from_options(options_from_str(
            "ekotrace-debug-collector \
            --session-id 0 \
            --little-endian \
            --big-endian \
            --attach stm32 \
            --interval 1s \
            --output-file ./out \
            0x100",
        )) {
            panic!("No error when specified both big and little endian")
        }
    }

    /// Default to little endian if none specified and no ELF given
    #[test]
    fn specify_neither_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                0x1"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1]
            }
        )
    }

    /// Imply endianness from ELF if not specified
    #[test]
    fn imply_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf \
                ./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example \
                0x1"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1]
            }
        );
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf ./tests/example-be-elf \
                0x1"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: true,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1]
            }
        )
    }

    /// Use specified endianness even if ELF is opposite
    #[test]
    fn use_specified_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --big-endian \
                --elf \
                ./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example \
                0x1"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: true,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1]
            }
        );
        assert_eq!(
            config_from_options(options_from_str(
                "ekotrace-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --little-endian \
                --elf ./tests/example-be-elf \
                0x1"
            ))
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                tracer_addrs: vec![0x1]
            }
        )
    }
}
