//! A small library which converts a process graph into a set of communicating processes.
//! ```
//! use std::{thread, time::Duration};
//!
//! use proc_graph::Network;
//!
//!     env_logger::init();
//!
//!     let mut net = Network::new();
//!
//!     net.add_process("a", vec!["b", "c"], |senders, _| loop {
//!         thread::sleep(Duration::from_secs(1));
//!         for (adj, s) in senders.iter() {
//!             println!("a is sending to {}", adj);
//!             s.send(("a".to_string(), ()))
//!                 .expect("shouldn't encounter a closed channel");
//!         }
//!     });
//!
//!     net.add_process("b", vec!["d"], |senders, receiver| loop {
//!         thread::sleep(Duration::from_secs(1));
//!         let (sender, _) = receiver
//!             .recv()
//!             .expect("shouldn't encounter a closed channel");
//!         println!("b received from {}", sender);
//!         for s in senders.values() {
//!             s.send(("b".to_string(), ()))
//!                 .expect("shouldn't encounter a closed channel");
//!         }
//!     });
//!
//!     net.add_process("c", vec!["d"], |senders, receiver| loop {
//!         thread::sleep(Duration::from_secs(1));
//!         let (sender, _) = receiver
//!             .recv()
//!             .expect("shouldn't encounter a closed channel");
//!         println!("c received from {}", sender);
//!         for s in senders.values() {
//!             s.send(("c".to_string(), ()))
//!                 .expect("shouldn't encounter a closed channel");
//!         }
//!     });
//!
//!     net.add_process("d", vec![], |_, receiver| loop {
//!         thread::sleep(Duration::from_secs(1));
//!         let (sender, _) = receiver
//!             .recv()
//!             .expect("shouldn't encounter a closed channel");
//!         println!("d received from {}", sender);
//!     });
//!
//!     net.start();
//! ```
use std::{
    collections::HashMap,
    sync::mpsc::{self, Receiver, Sender},
    thread::{self, JoinHandle},
};

/// A network of processes. Each process has a mailbox and the set of
/// addresses (senders) it needs to communicate with its neighbors.
#[derive(Default)]
pub struct Network<T> {
    procs: HashMap<String, Process<T>>,
}

impl<T> Network<T>
where
    T: Default + Send + 'static,
{
    pub fn new() -> Self {
        Network {
            procs: HashMap::new(),
        }
    }

    /// Adding a process to the network takes a name, its neighbors,
    /// and a closure which acts as _the entire body_ of this
    /// process. I.e., if you want the process to run forever, that
    /// loop has to be _inside_ the given closure.
    ///
    /// The process's neighbor's addresses (the senders) and the
    /// process's mailbox are passed into the closure. The only
    /// abstraction provided here is converting the given
    /// graph—described the process and its adjacencies—into mailboxes
    /// and addresses.
    pub fn add_process<'a, F>(&'a mut self, name: &'static str, adj: Vec<&'static str>, body: F)
    where
        F: Fn(HashMap<String, Sender<(String, T)>>, Receiver<(String, T)>) + Send + 'static,
    {
        let mut proc = {
            if let Some(mut p) = self.procs.remove(name) {
                p.adj = adj.into_iter().map(|a| a.to_string()).collect();
                p.body = Some(Box::new(body));
                p
            } else {
                let (s, r) = mpsc::channel();
                Process {
                    adj: adj.into_iter().map(|a| a.to_string()).collect(),
                    senders: HashMap::new(),
                    self_sender: s,
                    receiver: r,
                    body: Some(Box::new(body)),
                }
            }
        };
        for adj in proc.adj.iter() {
            let recv_proc = {
                if let Some(p) = self.procs.remove(adj) {
                    p
                } else {
                    let (s, r) = mpsc::channel();
                    Process {
                        adj: Vec::new(),
                        senders: HashMap::new(),
                        self_sender: s,
                        receiver: r,
                        body: None,
                    }
                }
            };
            proc.senders
                .insert(adj.to_string(), recv_proc.self_sender.clone());
            self.procs.insert(adj.clone(), recv_proc);
        }
        self.procs.insert(name.to_string(), proc);
    }

    /// Start the processes in this network. Blocks until all
    /// of the processes have finished.
    pub fn start_and_wait(self) {
        let mut handles = Vec::new();
        for (_, proc) in self.procs.into_iter() {
            handles.push(proc.run());
        }
        for handle in handles {
            handle.join().expect("joining running threads");
        }
    }

    /// Start the processes in this network.
    pub fn start(self) {
        for (_, proc) in self.procs.into_iter() {
            proc.run();
        }
    }
}

struct Process<T> {
    adj: Vec<String>,
    body: Option<
        Box<dyn Fn(HashMap<String, Sender<(String, T)>>, Receiver<(String, T)>) + Send + 'static>,
    >,
    senders: HashMap<String, Sender<(String, T)>>,
    self_sender: Sender<(String, T)>,
    receiver: Receiver<(String, T)>,
}

impl<T> Process<T>
where
    T: Default + Send + 'static,
{
    fn run(self) -> JoinHandle<()> {
        thread::spawn(move || {
            let body = self
                .body
                .expect("a graph should be complete before running its processes");
            body(self.senders, self.receiver);
        })
    }
}
