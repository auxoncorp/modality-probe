use std::{thread, time::Duration};

use log::info;

use proc_graph::Network;

fn main() {
    env_logger::init();

    let mut net = Network::new();

    net.add_process("a", vec!["b", "c"], |senders, _| loop {
        thread::sleep(Duration::from_secs(1));
        for (adj, s) in senders.iter() {
            info!("a is sending to {}", adj);
            s.send(("a".to_string(), ()))
                .expect("shouldn't encounter a closed channel");
        }
    });

    net.add_process("b", vec!["d"], |senders, receiver| loop {
        thread::sleep(Duration::from_secs(1));
        let (sender, _) = receiver
            .recv()
            .expect("shouldn't encounter a closed channel");
        info!("b received from {}", sender);
        for s in senders.values() {
            s.send(("b".to_string(), ()))
                .expect("shouldn't encounter a closed channel");
        }
    });

    net.add_process("c", vec!["d"], |senders, receiver| loop {
        thread::sleep(Duration::from_secs(1));
        let (sender, _) = receiver
            .recv()
            .expect("shouldn't encounter a closed channel");
        info!("c received from {}", sender);
        for s in senders.values() {
            s.send(("c".to_string(), ()))
                .expect("shouldn't encounter a closed channel");
        }
    });

    net.add_process("d", vec![], |_, receiver| loop {
        thread::sleep(Duration::from_secs(1));
        let (sender, _) = receiver
            .recv()
            .expect("shouldn't encounter a closed channel");
        info!("d received from {}", sender);
    });

    net.start_and_wait();
}
