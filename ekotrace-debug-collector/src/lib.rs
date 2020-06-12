use std::net::SocketAddrV4;
use std::path::PathBuf;
use std::time::Duration;

use util::model::SessionId;

#[derive(Debug, PartialEq)]
pub struct Config {
    pub session_id: SessionId,
    pub big_endian: bool,
    pub attach_target: Option<String>,
    pub gdb_addr: Option<SocketAddrV4>,
    pub interval: Duration,
    pub output_path: PathBuf,
    pub tracer_addrs: Vec<u32>
}
