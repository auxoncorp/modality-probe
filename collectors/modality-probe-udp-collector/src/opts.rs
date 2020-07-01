use crate::Config;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::path::PathBuf;
#[cfg(feature = "cli")]
use structopt::StructOpt;

pub const DEFAULT_PORT: u16 = 2718;

#[derive(Debug, Default)]
#[cfg_attr(feature = "cli", derive(StructOpt))]
#[cfg_attr(
    feature = "cli",
    structopt(
        name = "modality-probe-udp-collector",
        about = "Server that receives modality-probe reports via UDP and logs to file"
    )
)]
pub struct Opts {
    /// What localhost port is this server going to receive data on
    #[cfg_attr(feature = "cli", structopt(short = "p", long))]
    pub port: Option<u16>,

    /// Session id to associate with the collected trace data
    #[cfg_attr(feature = "cli", structopt(short = "s", long = "session-id"))]
    pub session_id: Option<u32>,

    /// Output file location
    #[cfg_attr(
        feature = "cli",
        structopt(short = "o", long = "output-file", parse(from_os_str))
    )]
    pub output_file: Option<PathBuf>,
}

impl From<Opts> for Config {
    fn from(o: Opts) -> Self {
        let session_id = o.session_id.unwrap_or(0);
        Config {
            addr: SocketAddr::V4(SocketAddrV4::new(
                Ipv4Addr::new(127, 0, 0, 1),
                o.port.unwrap_or(DEFAULT_PORT),
            )),
            session_id: session_id.into(),
            output_file: o.output_file.unwrap_or_else(|| {
                std::env::current_dir()
                    .expect("Could not retrieve current directory")
                    .join(format!("session_{}_log_entries.csv", session_id))
            }),
        }
    }
}
