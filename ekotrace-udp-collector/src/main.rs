use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::path::PathBuf;
#[cfg(feature = "cli")]
use structopt::StructOpt;

const DEFAULT_PORT: u16 = 2718;

#[derive(Debug, Default)]
#[cfg_attr(feature = "cli", derive(StructOpt))]
#[cfg_attr(
    feature = "cli",
    structopt(
        name = "ekotrace-udp-collector",
        about = "Server that receives ekotrace reports via UDP and logs to file"
    )
)]
pub struct CLIOptions {
    /// What localhost port is this server going to receive data on
    #[cfg_attr(feature = "cli", structopt(short = "p", long))]
    port: Option<u16>,

    /// Session id to associate with the collected trace data
    #[cfg_attr(feature = "cli", structopt(short = "s", long = "session-id"))]
    session_id: Option<u32>,

    /// Output file location
    #[cfg_attr(
        feature = "cli",
        structopt(short = "o", long = "output-file", parse(from_os_str))
    )]
    output_file: Option<PathBuf>,
}

impl From<CLIOptions> for ekotrace_udp_collector::Config {
    fn from(o: CLIOptions) -> Self {
        let session_id = o.session_id.unwrap_or(0);
        ekotrace_udp_collector::Config {
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

fn main() {
    #[cfg(not(feature = "cli"))]
    let opts = CLIOptions::default();
    #[cfg(feature = "cli")]
    let opts = CLIOptions::from_args();

    let config: ekotrace_udp_collector::Config = opts.into();
    println!("Running udp collector with configuration: {:#?}", config);
    let (_shutdown_sender, shutdown_receiver) =
        ekotrace_udp_collector::ShutdownSignalSender::new(config.addr);
    ekotrace_udp_collector::start_receiving(config, shutdown_receiver)
        .expect("Could not set up UDP Socket");
}
