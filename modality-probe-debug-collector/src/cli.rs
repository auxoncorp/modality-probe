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

use modality_probe_debug_collector::{Config, ProbeAddr};

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
    name = "modality-probe-debug-collector",
    about = "Periodically collects logs from microcontrollers over debug interfaces; outputs them to a file."
)]
pub struct CLIOptions {
    /// Session id to associate with the collected trace data
    #[structopt(short = "s", long = "session-id", default_value = "0")]
    session_id: u32,

    /// Specifies little endian architecture of target system
    #[structopt(short = "l", long = "little-endian", conflicts_with = "big-endian")]
    little_endian: bool,

    /// Specifies big endian architecture of target system
    #[structopt(short = "b", long = "big-endian")]
    big_endian: bool,

    /// Path of ELF file for endianness and symbol resolution
    #[structopt(short = "e", long = "elf", parse(from_os_str))]
    elf_path: Option<PathBuf>,

    /// Chip type of target system to attach to
    #[structopt(
        short = "a",
        long = "attach",
        conflicts_with = "gdb-addr",
        required_unless = "gdb-addr"
    )]
    attach_target: Option<String>,

    /// Address of gdb server to connect to
    #[structopt(short = "g", long = "gdb-addr", required_unless = "attach-target")]
    gdb_addr: Option<SocketAddrV4>,

    /// Interval between log collections. Ex: "2 min 15 sec 500 milli 250 micro"
    #[structopt(short = "i", long = "interval")]
    interval: String,

    /// Output file location
    #[structopt(short = "o", long = "output-file", parse(from_os_str))]
    output_path: PathBuf,

    /// Symbols and/or raw addresses of probes or probe pointers.
    /// Raw addresses should be in hex format, prefixed with '0x' or '0X'
    /// Probe pointer addresses and symbols should be prefixed with `*`.
    /// Ex: *0X100 0x104 symbol1 *symbol2 0X108 *0x10c
    probe_syms: Vec<String>,
}

/// Turn CLI options into configuration for the collector
pub(crate) fn config_from_options(options: CLIOptions) -> Result<Config, Box<dyn Error>> {
    let mut probe_addrs = Vec::new();
    let mut symbols = Vec::new();
    // Separate probe/probe pointer addresses and probe symbols
    for addr_str in options
        .probe_syms.iter()
    {
        match parse_probe_address(addr_str)? {
            None => symbols.push(addr_str),
            Some(probe_addr) => probe_addrs.push(probe_addr)
        }
    }
    
    let mut elf_endianness = None;
    if let Some(elf_path) = options.elf_path.as_ref() {
        let mut elf_buf = Vec::new();
        let elf_file = open_elf(&elf_path, &mut elf_buf)?;
        // Resolve symbol values
        for sym in symbols {
            if let Some((sym_val, _sym_size)) =
                parse_symbol_info(&elf_file, sym.trim_start_matches('*'))
            {
                if sym.starts_with('*') {
                    probe_addrs.push(ProbeAddr::PtrAddr(sym_val));
                } else {
                    probe_addrs.push(ProbeAddr::Addr(sym_val));
                }
            } else {
                return Err(Box::new(OptionsError::new(&format!(
                    "Could not find symbol value of \"{}\" in given ELF",
                    sym
                ))));
            }
        }
        elf_endianness = Some(elf_file.header.endianness());
    } else if !symbols.is_empty() {
        return Err(Box::new(OptionsError::new(
            "Must specify memory locations of probes or an ELF file to recover symbol values",
        )));
    }

    let interval = parse(&options.interval)?;

    Ok(modality_probe_debug_collector::Config {
        session_id: options.session_id.into(),
        big_endian: should_use_big_endian(&options, elf_endianness),
        attach_target: options.attach_target,
        gdb_addr: options.gdb_addr,
        interval,
        output_path: options.output_path,
        probe_addrs,
    })
}

/// Parse a probe address from a given argument, or return none in case of a symbol
fn parse_probe_address(input: &str) -> Result<Option<ProbeAddr>, Box<dyn Error>> {
    if input.starts_with("*0x") || input.starts_with("*0X") {
        let addr = u32::from_str_radix(input.trim_start_matches("*0x").trim_start_matches("*0X"), 16)?;
        Ok(Some(ProbeAddr::PtrAddr(addr)))
    } else if input.starts_with("0x") || input.starts_with("0X") {
        let addr = u32::from_str_radix(input.trim_start_matches("0x").trim_start_matches("0X"), 16)?;
        Ok(Some(ProbeAddr::Addr(addr)))
    } else {
        Ok(None)
    }
}

/// Open elf file for parsing
fn open_elf<'a>(path: &PathBuf, elf_buf: &'a mut Vec<u8>) -> Result<Elf<'a>, Box<dyn Error>> {
    let mut file = File::open(path)?;
    file.read_to_end(elf_buf)?;
    match Elf::parse(elf_buf) {
        Ok(elf) => Ok(elf),
        Err(err) => Err(Box::new(err)),
    }
}

/// Get value and size of given symbol, or None if symbol cannot be found
fn parse_symbol_info(elf_file: &Elf, symbol_name: &str) -> Option<(u32, u32)> {
    let log_sym = elf_file.syms.iter().find(|sym| -> bool {
        let name_opt = elf_file.strtab.get(sym.st_name);
        if let Some(Ok(name)) = name_opt {
            name == symbol_name
        } else {
            false
        }
    })?;
    Some((log_sym.st_value as u32, log_sym.st_size as u32))
}

/// Return whether or not big endian should be used based on specified endianness
/// and ELF endianness
fn should_use_big_endian(
    o: &CLIOptions,
    elf_endianness: Option<goblin::error::Result<Endian>>,
) -> bool {
    if !o.little_endian && !o.big_endian {
        // Imply endianness from ELF
        if let Some(endianness) = elf_endianness {
            match endianness {
                Ok(Endian::Little) => false,
                Ok(Endian::Big) => true,
                Err(_) => {
                    // Default to little endian with warning
                    println!(
                        "Warning: Endianness could not be parsed from ELF, using little endian"
                    );
                    false
                }
            }
        } else {
            // Default to little endian with warning
            println!("Warning: Endianness not specified, using little endian");
            false
        }
    } else if o.little_endian {
        if let Some(Ok(Endian::Big)) = elf_endianness {
            println!(
                "Warning: Little endian specified, but ELF is big endian. Using little endian."
            );
        }
        false
    } else {
        if let Some(Ok(Endian::Little)) = elf_endianness {
            println!("Warning: Big endian specified, but ELF is little endian. Using big endian.");
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::format;
    use std::fs::canonicalize;
    use std::process::Command;
    use std::str::FromStr;
    use std::time::Duration;
    use tempfile::{NamedTempFile, TempPath};

    const LE_SYMBOLS_BIN_PATH: &str =
        "./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example";
    const BE_BIN_RAW: [u8; 616] = [
        0x7f, 0x45, 0x4c, 0x46, 0x01, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x02, 0x00, 0x28, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x34, 0x00, 0x00, 0x01, 0x50, 0x05, 0x00, 0x02, 0x00, 0x00, 0x34, 0x00, 0x20, 0x00,
        0x03, 0x00, 0x28, 0x00, 0x07, 0x00, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x34,
        0xff, 0xff, 0xf0, 0x34, 0xff, 0xff, 0xf0, 0x34, 0x00, 0x00, 0x00, 0x60, 0x00, 0x00, 0x00,
        0x60, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
        0x00, 0x00, 0xff, 0xff, 0xf0, 0x00, 0xff, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x94, 0x00,
        0x00, 0x00, 0x94, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x10, 0x00, 0x64, 0x74, 0xe5, 0x51,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x00, 0x41, 0x00,
        0x00, 0x00, 0x2f, 0x61, 0x65, 0x61, 0x62, 0x69, 0x00, 0x01, 0x00, 0x00, 0x00, 0x25, 0x43,
        0x32, 0x2e, 0x30, 0x39, 0x00, 0x06, 0x0a, 0x07, 0x52, 0x08, 0x01, 0x09, 0x02, 0x0e, 0x00,
        0x11, 0x01, 0x14, 0x02, 0x15, 0x00, 0x17, 0x03, 0x18, 0x01, 0x19, 0x01, 0x22, 0x01, 0x26,
        0x01, 0x4c, 0x69, 0x6e, 0x6b, 0x65, 0x72, 0x3a, 0x20, 0x4c, 0x4c, 0x44, 0x20, 0x39, 0x2e,
        0x30, 0x2e, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0xff, 0xf1, 0x00, 0x2e, 0x64, 0x65, 0x62, 0x75, 0x67,
        0x5f, 0x61, 0x72, 0x61, 0x6e, 0x67, 0x65, 0x73, 0x00, 0x2e, 0x41, 0x52, 0x4d, 0x2e, 0x61,
        0x74, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x65, 0x73, 0x00, 0x2e, 0x63, 0x6f, 0x6d, 0x6d,
        0x65, 0x6e, 0x74, 0x00, 0x2e, 0x73, 0x79, 0x6d, 0x74, 0x61, 0x62, 0x00, 0x2e, 0x73, 0x68,
        0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0x00, 0x2e, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0x00,
        0x00, 0x34, 0x72, 0x35, 0x67, 0x64, 0x39, 0x73, 0x6b, 0x66, 0x68, 0x32, 0x33, 0x37, 0x66,
        0x6b, 0x62, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
        0x70, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x94, 0x00, 0x00, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x01, 0x00,
        0x00, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc4, 0x00, 0x00, 0x00, 0x12,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00, 0x29, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xd8, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x06, 0x00,
        0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x31,
        0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xf8, 0x00, 0x00, 0x00, 0x43, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3b, 0x00, 0x00, 0x00, 0x03, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x3b, 0x00, 0x00, 0x00, 0x12,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
        0x00,
    ];

    fn compile_symbol_example() {
        Command::new("cargo")
            .arg("build")
            .current_dir(canonicalize("./tests/symbols-example").unwrap())
            .output()
            .unwrap();
    }

    fn create_be_example() -> TempPath {
        let mut file = NamedTempFile::new().unwrap();
        file.as_file_mut().write(&BE_BIN_RAW).unwrap();
        file.into_temp_path()
    }

    fn options_from_str(input: &str) -> Result<CLIOptions, structopt::clap::Error> {
        CLIOptions::from_iter_safe(input.split(" "))
    }

    /// Test basic parsing
    #[test]
    fn test_basic() {
        assert_eq!(
            config_from_options(
                options_from_str(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                0x100"
                )
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x100)]
            }
        )
    }

    /// Specify gdb server instead of attach target
    #[test]
    fn specify_gdb_server() {
        assert_eq!(
            config_from_options(
                options_from_str(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --little-endian \
                --gdb-addr 127.0.0.1:3000 \
                --interval 1s \
                --output-file ./out \
                0x100"
                )
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: None,
                gdb_addr: Some(SocketAddrV4::from_str("127.0.0.1:3000").unwrap()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x100)]
            }
        )
    }

    /// Should error if both attach target and gdb server specified
    #[test]
    fn error_on_multiple_targets() {
        assert!(options_from_str(
            "modality-probe-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --gdb-server 127.0.0.1:3000 \
            --interval 1s \
            --output-file ./out \
            0x100",
        )
        .is_err());
    }

    /// Should error if neither attach target nor gdb server specified
    #[test]
    fn error_on_no_target() {
        assert!(options_from_str(
            "modality-probe-debug-collector \
            --session-id 0 \
            --little-endian \
            --interval 1s \
            --output-file ./out \
            0x100",
        )
        .is_err());
    }

    /// Should error if given ELF path does not exist
    #[test]
    fn error_elf_dne() {
        assert!(config_from_options(
            options_from_str(
                "modality-probe-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --elf ./nonexistent
            --interval 1s \
            --output-file ./out \
            0x100",
            )
            .unwrap()
        )
        .is_err());
    }

    /// Should error if given ELF path is not valid ELF file
    #[test]
    fn error_elf_invalid() {
        assert!(config_from_options(
            options_from_str(
                "modality-probe-debug-collector \
            --session-id 0 \
            --little-endian \
            --attach stm32 \
            --elf ./Cargo.toml
            --interval 1s \
            --output-file ./out \
            0x100",
            )
            .unwrap()
        )
        .is_err());
    }

    /// Symbol value parsing
    #[test]
    fn symbol_parsing() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                v1 v2 v3",
                    LE_SYMBOLS_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::Addr(0x20000000),
                    ProbeAddr::Addr(0x20000004),
                    ProbeAddr::Addr(0x20000008)
                ]
            }
        )
    }

    /// Input both symbols and addresses
    #[test]
    fn sym_addr_mix() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                0X1 v1 v2 0x10 v3 0X100",
                    LE_SYMBOLS_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::Addr(0x1),
                    ProbeAddr::Addr(0x10),
                    ProbeAddr::Addr(0x100),
                    ProbeAddr::Addr(0x20000000),
                    ProbeAddr::Addr(0x20000004),
                    ProbeAddr::Addr(0x20000008)
                ]
            }
        )
    }

    /// Should error if both big and little endian specified
    #[test]
    fn error_specify_both_endianness() {
        assert!(options_from_str(
            "modality-probe-debug-collector \
            --session-id 0 \
            --little-endian \
            --big-endian \
            --attach stm32 \
            --interval 1s \
            --output-file ./out \
            0x100",
        )
        .is_err());
    }

    /// Default to little endian if none specified and no ELF given
    #[test]
    fn specify_neither_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                0x1"
                )
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x1)]
            }
        )
    }

    /// Imply endianness from ELF if not specified
    #[test]
    fn imply_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                0x1",
                    LE_SYMBOLS_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x1)]
            }
        );

        let be_example_path = create_be_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                0x1",
                    be_example_path.to_str().unwrap()
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: true,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x1)]
            }
        )
    }

    /// Use specified endianness even if ELF is opposite
    #[test]
    fn use_specified_endianness() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --big-endian \
                --elf {} \
                0x1",
                    LE_SYMBOLS_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: true,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x1)]
            }
        );

        let be_example_path = create_be_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --little-endian \
                --elf {} \
                0x1",
                    be_example_path.to_str().unwrap()
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(0x1)]
            }
        )
    }

    /// Specify probe pointer addresses instead of probe addresses
    #[test]
    fn specify_probe_pointers() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                --session-id 0 \
                --little-endian \
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                *0X1 v1 *v2 *0x10 *v3 0x100",
                    LE_SYMBOLS_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                big_endian: false,
                attach_target: Some("stm32".to_string()),
                gdb_addr: None,
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::PtrAddr(0x1),
                    ProbeAddr::PtrAddr(0x10),
                    ProbeAddr::Addr(0x100),
                    ProbeAddr::Addr(0x20000000),
                    ProbeAddr::PtrAddr(0x20000004),
                    ProbeAddr::PtrAddr(0x20000008)
                ]
            }
        )
    }
}
