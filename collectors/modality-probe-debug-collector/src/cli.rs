use err_derive::Error;
use std::convert::TryFrom;
use std::fs::File;
use std::io::prelude::*;
use std::net::SocketAddrV4;
use std::path::PathBuf;
use structopt::StructOpt;

use goblin::elf::Elf;

use modality_probe_debug_collector::{Config, ProbeAddr, Target, Word};

#[derive(Debug, Error)]
pub enum CLIError {
    #[error(display = "Error parsing malformed address: \"{}\"", _0)]
    AddressNotValid(String),
    #[error(display = "Given address/symbol larger than expected size: \"{}\"", _0)]
    AddressTooBig(String),
    #[error(display = "Error opening ELF file")]
    ElfError,
    #[error(display = "Symbols were given but no elf file was specified")]
    MissingElfError,
    #[error(display = "Given interval not a valid duration: {}", _0)]
    InvalidInterval(String),
    #[error(display = "Symbol not found in given ELF file: \"{}\"", _0)]
    SymbolNotFound(String),
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

    /// Specifies 32 bit architecture of target system
    #[structopt(short = "32", long = "32-bit", conflicts_with = "word-size-64")]
    word_size_32: bool,

    /// Specifies 32 bit architecture of target system
    #[structopt(short = "64", long = "64-bit")]
    word_size_64: bool,

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
    attach: Option<String>,

    /// Address of gdb server to connect to
    #[structopt(short = "g", long = "gdb-addr", required_unless = "attach")]
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
pub(crate) fn config_from_options(options: CLIOptions) -> Result<Config, CLIError> {
    let mut probe_addrs = Vec::new();
    let mut symbols = Vec::new();

    let mut elf_buf = Vec::new();
    let (use_64_bit, elf_file_opt) = if let Some(elf_path) = options.elf_path.as_ref() {
        let elf_file = open_elf(&elf_path, &mut elf_buf)?;
        let use_64_bit = if !options.word_size_32 && !options.word_size_64 {
            const HEADER_SIZE_32: u16 = 52;
            const HEADER_SIZE_64: u16 = 64;
            let header_size = elf_file.header.e_ehsize;
            assert!(header_size == HEADER_SIZE_32 || header_size == HEADER_SIZE_64);
            header_size == HEADER_SIZE_64
        } else {
            options.word_size_64
        };
        (use_64_bit, Some(elf_file))
    } else {
        // Use 32 bit unless otherwise specified
        if !options.word_size_32 && !options.word_size_64 {
            println!("Warning: Pointer width not specified; using 32 bit");
        }
        (options.word_size_64, None)
    };

    for addr_str in options.probe_syms.iter() {
        match parse_probe_address(addr_str, use_64_bit)? {
            None => symbols.push(addr_str),
            Some(probe_addr) => probe_addrs.push(probe_addr),
        }
    }

    if let Some(elf_file) = elf_file_opt {
        for sym in symbols {
            let sym_val = parse_symbol_info(&elf_file, sym.trim_start_matches('*'), use_64_bit)?;
            if sym.starts_with('*') {
                probe_addrs.push(ProbeAddr::PtrAddr(sym_val));
            } else {
                probe_addrs.push(ProbeAddr::Addr(sym_val));
            }
        }
    } else if !symbols.is_empty() {
        return Err(CLIError::MissingElfError);
    }

    let interval = parse_duration::parse(&options.interval)
        .map_err(|_e| CLIError::InvalidInterval(options.interval.to_string()))?;

    let target = if let Some(probe_rs_target) = options.attach {
        Target::ProbeRsTarget(probe_rs_target)
    } else if let Some(gdb_addr) = options.gdb_addr {
        Target::GdbAddr(gdb_addr)
    } else {
        // StructOpt will exit if neither are provided
        unreachable!()
    };

    Ok(modality_probe_debug_collector::Config {
        session_id: options.session_id.into(),
        target,
        interval,
        output_path: options.output_path,
        probe_addrs,
    })
}

/// Parse a probe address from a given argument, or return none in case of a symbol
fn parse_probe_address(input: &str, use_64_bit: bool) -> Result<Option<ProbeAddr>, CLIError> {
    let is_address = ["0x", "0X", "*0x", "*0X"]
        .iter()
        .any(|prefix| input.starts_with(prefix));
    if !is_address {
        // Input is a symbol
        return Ok(None);
    }

    let trimmed = input
        .trim_start_matches("*0x")
        .trim_start_matches("*0X")
        .trim_start_matches("0x")
        .trim_start_matches("0X");
    let addr = u64::from_str_radix(trimmed, 16)
        .map_err(|_e| CLIError::AddressNotValid(input.to_string()))?;
    let addr_word = if use_64_bit {
        Word::U64(addr)
    } else {
        let addr_32 =
            u32::try_from(addr).map_err(|_e| CLIError::AddressTooBig(input.to_string()))?;
        Word::U32(addr_32)
    };
    if input.starts_with("*") {
        Ok(Some(ProbeAddr::PtrAddr(addr_word)))
    } else {
        Ok(Some(ProbeAddr::Addr(addr_word)))
    }
}

/// Open elf file for parsing
fn open_elf<'a>(path: &PathBuf, elf_buf: &'a mut Vec<u8>) -> Result<Elf<'a>, CLIError> {
    let mut file = File::open(path).map_err(|_e| CLIError::ElfError)?;
    file.read_to_end(elf_buf).map_err(|_e| CLIError::ElfError)?;
    Elf::parse(elf_buf).map_err(|_e| CLIError::ElfError)
}

/// Get value and size of given symbol, or None if symbol cannot be found
fn parse_symbol_info(
    elf_file: &Elf,
    symbol_name: &str,
    use_64_bit: bool,
) -> Result<Word, CLIError> {
    let log_sym = elf_file
        .syms
        .iter()
        .find(|sym| -> bool {
            let name_opt = elf_file.strtab.get(sym.st_name);
            if let Some(Ok(name)) = name_opt {
                name == symbol_name
            } else {
                false
            }
        })
        .ok_or(CLIError::SymbolNotFound(symbol_name.to_string()))?;
    if use_64_bit {
        Ok(Word::U64(log_sym.st_value))
    } else {
        let val_32 = u32::try_from(log_sym.st_value)
            .map_err(|_e| CLIError::AddressTooBig(symbol_name.to_string()))?;
        Ok(Word::U32(val_32))
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

    const SYMBOLS_32_BIN_PATH: &str =
        "./tests/symbols-example/target/thumbv7em-none-eabihf/debug/symbols-example";
    const EMPTY_BIN_PATH: &str = "./tests/empty-example/target/debug/empty-example";

    fn compile_symbol_example() {
        Command::new("cargo")
            .arg("build")
            .current_dir(canonicalize("./tests/symbols-example").unwrap())
            .output()
            .unwrap();
    }

    fn compile_empty_example() {
        Command::new("cargo")
            .arg("build")
            .current_dir(canonicalize("./tests/empty-example").unwrap())
            .output()
            .unwrap();
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
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(Word::U32(0x100))]
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
                target: Target::GdbAddr(SocketAddrV4::from_str("127.0.0.1:3000").unwrap()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(Word::U32(0x100))]
            }
        )
    }

    /// Should error if both attach target and gdb server specified
    #[test]
    fn error_on_multiple_targets() {
        assert!(options_from_str(
            "modality-probe-debug-collector \
            --session-id 0 \
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
            --attach stm32 \
            --elf ./nonexistent
            --interval 1s \
            --output-file ./out \
            0x100 symbol",
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
            --attach stm32 \
            --elf ./Cargo.toml
            --interval 1s \
            --output-file ./out \
            0x100 symbol",
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
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --32-bit \
                --elf {} \
                v1 v2 v3",
                    SYMBOLS_32_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::Addr(Word::U32(0x20000000)),
                    ProbeAddr::Addr(Word::U32(0x20000004)),
                    ProbeAddr::Addr(Word::U32(0x20000008))
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
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                --32-bit \
                0X1 v1 v2 0x10 v3 0X100",
                    SYMBOLS_32_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::Addr(Word::U32(0x1)),
                    ProbeAddr::Addr(Word::U32(0x10)),
                    ProbeAddr::Addr(Word::U32(0x100)),
                    ProbeAddr::Addr(Word::U32(0x20000000)),
                    ProbeAddr::Addr(Word::U32(0x20000004)),
                    ProbeAddr::Addr(Word::U32(0x20000008))
                ]
            }
        )
    }

    /// Should error if both big and little endian specified
    #[test]
    fn error_specify_both_ptr_width() {
        assert!(options_from_str(
            "modality-probe-debug-collector \
            --session-id 0 \
            --64-bit \
            --32-bit \
            --attach stm32 \
            --interval 1s \
            --output-file ./out \
            0x100",
        )
        .is_err());
    }

    /// Imply endianness from ELF as 64 bit, even if not specified in cli args
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn imply_word_size_64() {
        compile_empty_example();
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
                    EMPTY_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![ProbeAddr::Addr(Word::U64(0x1))]
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
                --attach stm32 \
                --interval 1s \
                --output-file ./out \
                --elf {} \
                *0X1 v1 *v2 *0x10 *v3 0x100",
                    SYMBOLS_32_BIN_PATH
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::PtrAddr(Word::U32(0x1)),
                    ProbeAddr::PtrAddr(Word::U32(0x10)),
                    ProbeAddr::Addr(Word::U32(0x100)),
                    ProbeAddr::Addr(Word::U32(0x20000000)),
                    ProbeAddr::PtrAddr(Word::U32(0x20000004)),
                    ProbeAddr::PtrAddr(Word::U32(0x20000008))
                ]
            }
        )
    }

    /// Specify probe pointer addresses instead of probe addresses
    #[test]
    fn specify_probe_pointers_64() {
        compile_symbol_example();
        assert_eq!(
            config_from_options(
                options_from_str(&format!(
                    "modality-probe-debug-collector \
                    --session-id 0 \
                    --attach stm32 \
                    --interval 1s \
                    --output-file ./out \
                    --64-bit \
                    *0X1 0x10 *0x100"
                ))
                .unwrap()
            )
            .unwrap(),
            Config {
                session_id: 0.into(),
                target: Target::ProbeRsTarget("stm32".to_string()),
                interval: Duration::from_millis(1000),
                output_path: "./out".into(),
                probe_addrs: vec![
                    ProbeAddr::PtrAddr(Word::U64(0x1)),
                    ProbeAddr::Addr(Word::U64(0x10)),
                    ProbeAddr::PtrAddr(Word::U64(0x100)),
                ]
            }
        )
    }
}
