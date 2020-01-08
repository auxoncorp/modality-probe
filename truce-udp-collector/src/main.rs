use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::path::PathBuf;

const DEFAULT_PORT: u16 = 2718;

#[derive(Default)]
struct CLIOptions {
    port: Option<u16>,
    session_id: Option<u32>,
    output_file: Option<PathBuf>
}

impl CLIOptions {
    fn from_args() -> Self {
        let args: Vec<String> = std::env::args().collect();
        let mut options : CLIOptions = Default::default();
        for pair in args.windows(2) {
            if pair[0] == "-p" || pair[0] == "--port" {
                options.port = Some(pair[1].parse().expect("Invalid local port to receive on."))
            }
            if pair[0] == "-s" || pair[0] == "--session-id" {
                options.session_id = Some(pair[1].parse().expect("Invalid unsigned integer session id."))
            }
            if pair[0] == "-o" || pair[0] == "--output" || pair[0] == "--output-file" {
                options.output_file = Some(pair[1].parse().expect("Invalid unsigned integer session id."))
            }
        }
        options
    }
}

impl From<CLIOptions> for truce_udp_collector::Config {
    fn from(o: CLIOptions) -> Self {
        let session_id = o.session_id.unwrap_or(0);
        truce_udp_collector::Config {
            addr: SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), o.port.unwrap_or(DEFAULT_PORT))),
            session_id: session_id.into(),
            output_file: o.output_file.unwrap_or_else(|| {
                std::env::current_dir().expect("Could not retrieve current directory")
                    .join(format!("session_{}_log_entries.csv", session_id))
            }),
        }
    }
}

fn main() {
    let config = CLIOptions::from_args().into();
    println!("Running udp collector with configuration: {:#?}", config);
    truce_udp_collector::start_receiving(config).expect("Could not set up UDP Socket");
    println!("TODO - error code piping");
}
