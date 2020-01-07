use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

fn main() {
    let port: u16 = match std::env::args().nth(1) {
        Some(port_str) => port_str.parse().expect("Invalid local port to receive on"),
        None => 2718,
    };
    truce_udp_collector::start_receiving_at_addr(SocketAddr::V4(SocketAddrV4::new(
        Ipv4Addr::new(127, 0, 0, 1),
        port,
    )))
    .expect("Could not set up UDP Socket");
    println!("TODO - error code piping");
}
