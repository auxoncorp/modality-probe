use std::convert::TryFrom;
use std::{
    io::{Error as IoError, Write},
    net::{SocketAddr, UdpSocket},
    path::PathBuf,
};

use chrono::Utc;

use modality_probe_collector_common::{self as common, json, Report, ReportLogEntry, SessionId};

mod opts;

pub use opts::*;

#[derive(Debug, PartialEq)]
pub struct Config {
    pub addr: SocketAddr,
    pub session_id: SessionId,
    pub output_file: PathBuf,
}

pub struct ShutdownSignalSender {
    pub sender: std::sync::mpsc::Sender<()>,
    pub server_addr: SocketAddr,
}

const OS_PICK_ADDR_HINT: &str = "0.0.0.0:0";

pub type ShutdownSignalReceiver = std::sync::mpsc::Receiver<()>;

impl ShutdownSignalSender {
    pub fn new(server_addr: SocketAddr) -> (ShutdownSignalSender, ShutdownSignalReceiver) {
        let (sender, receiver) = std::sync::mpsc::channel();
        (
            ShutdownSignalSender {
                sender,
                server_addr,
            },
            receiver,
        )
    }

    pub fn shutdown(&self) {
        if self.sender.send(()).is_err() {
            // The server side receiving the message is already gone
            return;
        }
        if let Ok(socket) = UdpSocket::bind(OS_PICK_ADDR_HINT) {
            // Try to send a dummy byte to kick the server's silly synchronous
            // receive loop
            let _ = socket.send_to(&[0], self.server_addr);
        }
    }
}

pub fn start_receiving(
    config: Config,
    shutdown_signal_receiver: ShutdownSignalReceiver,
) -> Result<(), IoError> {
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(config.output_file)?;
    start_receiving_at_addr(
        config.addr,
        config.session_id,
        &mut file,
        shutdown_signal_receiver,
    )
}

pub fn start_receiving_at_addr<W: Write>(
    addr: SocketAddr,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal_receiver: ShutdownSignalReceiver,
) -> Result<(), IoError> {
    start_receiving_from_socket(
        UdpSocket::bind(addr)?,
        session_id,
        log_output_writer,
        shutdown_signal_receiver,
    );
    Ok(())
}

pub fn start_receiving_from_socket<W: Write>(
    socket: UdpSocket,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal_receiver: ShutdownSignalReceiver,
) {
    let addr = socket.local_addr().map(|a| a.to_string());
    let mut buf = vec![0u8; 1024 * 1024];
    let mut log_entries_buffer: Vec<ReportLogEntry> = Vec::with_capacity(4096);
    loop {
        if shutdown_signal_receiver.try_recv().is_ok() {
            return;
        }
        // Be sure to zero out the first few bytes to ensure that the
        // magic fingerprint words are not stale.
        for b in buf[..8].iter_mut() {
            *b = 0;
        }
        let (bytes_read, _src) = match socket.recv_from(&mut buf) {
            Ok(r) => r,
            Err(e) => {
                match addr.as_ref() {
                    Ok(a) => eprintln!("Error during recv_from on {} : {}", a, e),
                    Err(_) => eprintln!("Error during recv_from : {}", e),
                }
                continue;
            }
        };
        if bytes_read == 1 && buf[0] == 0 {
            // Dummy byte received solely for the purpose of kicking the server's recv loop
            // during a shutdown
            continue;
        }
        let receive_time = Utc::now();

        // N.B. If we were feeling bottlenecked, hand off the read bytes to another thread
        // N.B. If we were feeling fancy, do said handoff by reading directly into a rotating preallocated
        // slot in a concurrent queue, ala LMAX Disruptor

        // N.B. To avoid copies and allocation, skip materializing a log report
        // and instead directly create log entries. Probably wise to wait until the
        // log format settles down some before doing this.
        log_entries_buffer.clear();

        match Report::try_from(&buf[..bytes_read]) {
            Ok(log_report) => {
                if let Err(e) = common::add_log_report_to_entries(
                    &log_report,
                    session_id,
                    receive_time,
                    &mut log_entries_buffer,
                ) {
                    eprintln!(
                        "Encountered a malformed report, not adding it to the trace: {}",
                        e
                    )
                }
            }
            Err(_) => {
                eprintln!(
                    "Error parsing a message as a report, throwing away {} bytes",
                    bytes_read
                );

                continue;
            }
        }

        if let Err(e) = json::write_log_entries(log_output_writer, &log_entries_buffer) {
            eprintln!("Error writing log entries: {}", e);
        }
        let _ = log_output_writer.flush();
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        convert::TryInto,
        net::{Ipv4Addr, SocketAddrV4, TcpListener},
        sync::{
            atomic::{AtomicU16, AtomicU32, Ordering},
            Mutex,
        },
        thread,
    };

    use chrono::DateTime;
    use lazy_static::*;
    use pretty_assertions::assert_eq;

    use modality_probe::time::{NanosecondResolution, WallClockId};
    use modality_probe::*;
    use modality_probe_collector_common::*;

    use super::*;
    use std::mem::MaybeUninit;

    fn dummy_report(raw_main_probe_id: u32) -> Report {
        Report {
            probe_id: ProbeId::new(raw_main_probe_id).unwrap(),
            probe_clock: LogicalClock {
                id: ProbeId::new(2).unwrap(),
                epoch: ProbeEpoch(1),
                ticks: ProbeTicks(1),
            },
            seq_num: 1.into(),
            persistent_epoch_counting: false,
            time_resolution: NanosecondResolution::UNSPECIFIED,
            wall_clock_id: WallClockId::default(),
            frontier_clocks: vec![LogicalClock {
                id: ProbeId::new(raw_main_probe_id).unwrap(),
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            }],
            event_log: vec![
                EventLogEntry::Event(EventId::new(2).unwrap()),
                EventLogEntry::TraceClock(LogicalClock {
                    id: ProbeId::new(2).unwrap(),
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                }),
                EventLogEntry::TraceClock(LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
            ],
        }
    }

    fn report_and_matching_entries(
        raw_main_probe_id: u32,
        session_id: SessionId,
        receive_time: DateTime<Utc>,
    ) -> (Report, Vec<ReportLogEntry>) {
        let main_probe_id = raw_main_probe_id.try_into().unwrap();
        let rep = dummy_report(raw_main_probe_id);
        let entries = vec![
            ReportLogEntry {
                session_id,
                sequence_number: 1.into(),
                sequence_index: 0,
                probe_id: main_probe_id,
                persistent_epoch_counting: rep.persistent_epoch_counting,
                time_resolution: rep.time_resolution,
                wall_clock_id: rep.wall_clock_id,
                data: LogEntryData::FrontierClock(LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                clock: LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                receive_time,
            },
            ReportLogEntry {
                session_id,
                sequence_number: 1.into(),
                sequence_index: 1,
                probe_id: main_probe_id,
                persistent_epoch_counting: rep.persistent_epoch_counting,
                time_resolution: rep.time_resolution,
                wall_clock_id: rep.wall_clock_id,
                data: LogEntryData::Event(EventId::new(2).unwrap()),
                clock: LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                },
                receive_time,
            },
            ReportLogEntry {
                session_id,
                sequence_number: 1.into(),
                sequence_index: 2,
                probe_id: main_probe_id,
                persistent_epoch_counting: rep.persistent_epoch_counting,
                time_resolution: rep.time_resolution,
                wall_clock_id: rep.wall_clock_id,
                data: LogEntryData::TraceClock(LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                }),
                clock: LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                receive_time,
            },
            ReportLogEntry {
                session_id,
                sequence_number: 1.into(),
                sequence_index: 3,
                probe_id: main_probe_id,
                persistent_epoch_counting: rep.persistent_epoch_counting,
                time_resolution: rep.time_resolution,
                wall_clock_id: rep.wall_clock_id,
                data: LogEntryData::TraceClock(LogicalClock {
                    id: ProbeId::new(1).unwrap(),
                    epoch: ProbeEpoch(0),
                    ticks: ProbeTicks(0),
                }),
                clock: LogicalClock {
                    id: main_probe_id,
                    epoch: ProbeEpoch(1),
                    ticks: ProbeTicks(1),
                },
                receive_time,
            },
        ];
        (rep, entries)
    }

    #[test]
    fn log_report_to_entries() {
        let raw_main_probe_id = 2;
        let session_id = 81.into();
        let receive_time = Utc::now();
        let (report, expected_entries) =
            report_and_matching_entries(raw_main_probe_id, session_id, receive_time);
        let mut entries = Vec::new();
        add_log_report_to_entries(&report, session_id, receive_time, &mut entries).unwrap();
        assert_eq!(4, entries.len());
        for (idx, e) in entries.iter().enumerate() {
            assert_eq!(idx, e.sequence_index as usize);
        }
        assert_eq!(expected_entries, entries);
    }
    lazy_static! {
        static ref ACTIVE_TEST_PORTS: Mutex<HashSet<u16>> = Mutex::new(Default::default());
    }
    static STARTING_PORT: AtomicU16 = AtomicU16::new(8000);

    fn find_usable_addrs(limit: usize) -> Vec<SocketAddr> {
        let start_at = STARTING_PORT.load(Ordering::SeqCst);
        let mut ports = ACTIVE_TEST_PORTS.lock().unwrap();
        (start_at..start_at + 1000)
            .filter_map(|port| {
                if ports.contains(&port) {
                    return None;
                }
                let addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), port));
                if let Ok(tcp_binding) = TcpListener::bind(addr) {
                    STARTING_PORT.store(port + 1, Ordering::SeqCst);
                    ports.insert(port);
                    std::mem::drop(tcp_binding);
                    if UdpSocket::bind(addr).is_ok() {
                        Some(addr)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .take(limit)
            .collect()
    }

    #[derive(Copy, Clone, Debug, PartialEq)]
    enum ServerState {
        Started,
        Shutdown,
    }
    static TICKING_SESSION_ID: AtomicU32 = AtomicU32::new(314);
    fn gen_session_id() -> u32 {
        TICKING_SESSION_ID.fetch_add(1, Ordering::SeqCst)
    }

    #[test]
    fn minimal_round_trip() {
        let addrs = find_usable_addrs(2);
        let server_addr = *addrs.first().unwrap();
        let (shutdown_sender, shutdown_receiver) = ShutdownSignalSender::new(server_addr);
        let (server_state_sender, server_state_receiver) = crossbeam::unbounded();
        let session_id = gen_session_id().into();
        let f = tempfile::NamedTempFile::new().expect("Could not make temp file");
        let output_file_path = PathBuf::from(f.path());
        let config = Config {
            addr: server_addr,
            session_id,
            output_file: output_file_path.clone(),
        };
        let h = std::thread::spawn(move || {
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(config.output_file)
                .expect("Could not open file for writing");
            let socket = UdpSocket::bind(config.addr).expect("Could not bind to server socket");
            server_state_sender
                .send(ServerState::Started)
                .expect("Could not send status update");
            start_receiving_from_socket(socket, config.session_id, &mut file, shutdown_receiver);
            let _ = server_state_sender.send(ServerState::Shutdown);
        });
        thread::yield_now();

        let log_report = dummy_report(31);
        if let ServerState::Started = server_state_receiver
            .recv()
            .expect("Could not get state update")
        {
            let mut lcm_log_report = [0u8; 1024];
            let lcm_bytes = log_report
                .write_into_le_bytes(&mut lcm_log_report)
                .expect("Could not write log report as lcm");
            let client_addr = addrs[1];
            let socket =
                UdpSocket::bind(client_addr).expect("Could not bind to socket for sending");
            socket
                .send_to(&lcm_log_report[..lcm_bytes], server_addr)
                .expect("Could not send lcm bytes");
            thread::sleep(std::time::Duration::from_millis(200));
            shutdown_sender.shutdown();
        } else {
            panic!("Server did not start up");
        }

        let ss = server_state_receiver
            .recv()
            .expect("Could not get state update");
        if ss != ServerState::Shutdown {
            panic!("Expected the server to have shut down");
        }
        let mut file_reader =
            std::fs::File::open(&output_file_path).expect("Could not open output file for reading");
        let found_log_entries = json::read_log_entries(&mut file_reader)
            .expect("Could not read output file as json log entries");

        let expected_entries: usize = log_report.frontier_clocks.len() + log_report.event_log.len();
        assert_eq!(expected_entries, found_log_entries.len());

        let found_entry_ids: HashSet<_> = found_log_entries
            .iter()
            .map(|e| (e.session_id, e.sequence_number, e.sequence_index))
            .collect();
        assert_eq!(
            expected_entries,
            found_entry_ids.len(),
            "All entries must have unique id tuples"
        );

        for e in found_log_entries.iter() {
            assert_eq!(session_id, e.session_id);
            assert_eq!(log_report.probe_id, e.probe_id);
        }
        h.join().expect("Couldn't join server handler thread");
    }

    const SNAPSHOT_BYTES_SIZE: usize = 12;
    const PROBE_STORAGE_BYTES_SIZE: usize = 512;
    const LOG_REPORT_BYTES_SIZE: usize = 512;

    #[test]
    fn linear_triple_inferred_unreporting_middleman_graph() {
        let addrs = find_usable_addrs(1);
        let server_addr = addrs[0];
        let (shutdown_sender, shutdown_receiver) = ShutdownSignalSender::new(server_addr);
        let (server_state_sender, server_state_receiver) = crossbeam::bounded(0);
        let session_id = gen_session_id().into();
        let f = tempfile::NamedTempFile::new().expect("Could not make temp file");
        let output_file_path = PathBuf::from(f.path());
        let config = Config {
            addr: server_addr,
            session_id,
            output_file: output_file_path.clone(),
        };
        let h = thread::spawn(move || {
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(config.output_file)
                .expect("Could not open file for writing");
            let socket = UdpSocket::bind(config.addr).expect("Could not bind to server socket");
            server_state_sender
                .send(ServerState::Started)
                .expect("Could not send status update");
            start_receiving_from_socket(socket, config.session_id, &mut file, shutdown_receiver);
            let _ = server_state_sender.send(ServerState::Shutdown);
        });
        thread::yield_now();
        assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
        let mut net = proc_graph::Network::new();
        let probe_a_id = modality_probe::ProbeId::new(131).unwrap();
        let probe_b_id = modality_probe::ProbeId::new(141).unwrap();
        let probe_c_id = modality_probe::ProbeId::new(159).unwrap();
        let event_foo = EventLogEntry::Event(modality_probe::EventId::new(7).unwrap());
        let event_bar = EventLogEntry::Event(modality_probe::EventId::new(23).unwrap());
        let event_baz = EventLogEntry::Event(modality_probe::EventId::new(29).unwrap());
        const NUM_MESSAGES_FROM_A: usize = 11;

        let (network_done_sender, network_done_receiver) = crossbeam::bounded(0);
        net.add_process(
            "a",
            vec!["b"],
            make_message_broadcaster_proc(
                "a",
                probe_a_id,
                NUM_MESSAGES_FROM_A,
                server_addr,
                Some(event_foo),
            ),
        );
        net.add_process(
            "b",
            vec!["c"],
            make_message_relay_proc("b", probe_b_id, NUM_MESSAGES_FROM_A, None, Some(event_bar)),
        );
        net.add_process(
            "c",
            vec![],
            make_message_sink_proc(
                probe_c_id,
                NUM_MESSAGES_FROM_A,
                SendLogReportEveryFewMessages {
                    n_messages: 3,
                    collector_addr: server_addr,
                },
                Some(event_baz),
                network_done_sender,
            ),
        );
        net.start();
        thread::yield_now();

        assert_eq!(Ok(()), network_done_receiver.recv());
        // Thanks, UDP
        std::thread::sleep(std::time::Duration::from_millis(200));
        shutdown_sender.shutdown();
        assert_eq!(Ok(ServerState::Shutdown), server_state_receiver.recv());

        h.join().expect("Couldn't join server handler thread");

        let mut file_reader =
            std::fs::File::open(&output_file_path).expect("Could not open output file for reading");
        let found_log_entries = json::read_log_entries(&mut file_reader)
            .expect("Could not read output file as json log entries");

        assert!(found_log_entries.len() > 0);
        let expected_direct_probe_ids: HashSet<_> =
            [probe_a_id, probe_c_id].iter().copied().collect();
        let built_in_event_ids: HashSet<_> =
            modality_probe::EventId::INTERNAL_EVENTS.iter().collect();
        for e in found_log_entries {
            assert_eq!(session_id, e.session_id);
            assert!(expected_direct_probe_ids.contains(&e.probe_id));
            match e.data {
                LogEntryData::Event(event) => {
                    // Event bar is logged only on b, and thus lost
                    if EventLogEntry::Event(event) == event_bar {
                        panic!("How the heck did bar get over there?");
                    }
                    if e.probe_id.get_raw() == probe_a_id.get_raw() {
                        // Process A should only be writing about event foo or the probe internal events
                        assert!(
                            EventLogEntry::Event(event) == event_foo
                                || built_in_event_ids.contains(&event)
                        );
                    } else if e.probe_id.get_raw() == probe_c_id.get_raw() {
                        // Process C should only be writing about event baz or the probe internals events
                        assert!(
                            EventLogEntry::Event(event) == event_baz
                                || built_in_event_ids.contains(&event),
                            "unexpected event for entry: {:?}",
                            e
                        );
                    }
                }
                LogEntryData::EventWithPayload(_, _) => (),
                LogEntryData::FrontierClock(lc) => {
                    if e.probe_id == probe_a_id {
                        // Process A should only know about itself, since it doesn't receive history from anyone else
                        assert_eq!(lc.id, probe_a_id);
                    } else if e.probe_id == probe_c_id {
                        // Process C should have clocks for itself and its direct precursor, B
                        assert!(lc.id == probe_c_id || lc.id == probe_b_id);
                    }
                }
                LogEntryData::TraceClock(lc) => {
                    if e.probe_id == probe_a_id {
                        assert_eq!(lc.id, probe_a_id);
                    } else if e.probe_id == probe_c_id {
                        assert!(lc.id == probe_c_id || lc.id == probe_b_id);
                    }
                }
                LogEntryData::WallClockTime(_) => (),
                LogEntryData::EventWithTime(_, _) => (),
                LogEntryData::EventWithPayloadWithTime(_, _, _) => (),
                LogEntryData::TraceClockWithTime(_, _) => (),
            }
        }
    }

    #[test]
    fn linear_pair_graph() {
        let addrs = find_usable_addrs(1);
        let server_addr = addrs[0];
        let (shutdown_sender, shutdown_receiver) = ShutdownSignalSender::new(server_addr);
        let (server_state_sender, server_state_receiver) = crossbeam::bounded(0);
        let session_id = gen_session_id().into();
        let f = tempfile::NamedTempFile::new().expect("Could not make temp file");
        let output_file_path = PathBuf::from(f.path());
        let config = Config {
            addr: server_addr,
            session_id,
            output_file: output_file_path.clone(),
        };
        let h = thread::spawn(move || {
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(config.output_file)
                .expect("Could not open file for writing");
            let socket = UdpSocket::bind(config.addr).expect("Could not bind to server socket");
            server_state_sender
                .send(ServerState::Started)
                .expect("Could not send status update");
            start_receiving_from_socket(socket, config.session_id, &mut file, shutdown_receiver);
            let _ = server_state_sender.send(ServerState::Shutdown);
        });
        thread::yield_now();
        assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
        let mut net = proc_graph::Network::new();
        let probe_a_id = modality_probe::ProbeId::new(31).unwrap();
        let probe_b_id = modality_probe::ProbeId::new(41).unwrap();
        let event_foo = EventLogEntry::Event(modality_probe::EventId::new(7).unwrap());
        let event_bar = EventLogEntry::Event(modality_probe::EventId::new(23).unwrap());
        const NUM_MESSAGES_FROM_A: usize = 11;

        let (network_done_sender, network_done_receiver) = crossbeam::bounded(0);
        net.add_process(
            "a",
            vec!["b"],
            make_message_broadcaster_proc(
                "a",
                probe_a_id,
                NUM_MESSAGES_FROM_A,
                server_addr,
                Some(event_foo),
            ),
        );
        net.add_process(
            "b",
            vec![],
            make_message_sink_proc(
                probe_b_id,
                NUM_MESSAGES_FROM_A,
                SendLogReportEveryFewMessages {
                    n_messages: 3,
                    collector_addr: server_addr,
                },
                Some(event_bar),
                network_done_sender,
            ),
        );
        net.start();
        thread::yield_now();

        assert_eq!(Ok(()), network_done_receiver.recv());
        // Thanks, UDP
        std::thread::sleep(std::time::Duration::from_millis(200));
        shutdown_sender.shutdown();
        assert_eq!(Ok(ServerState::Shutdown), server_state_receiver.recv());

        h.join().expect("Couldn't join server handler thread");

        let mut file_reader =
            std::fs::File::open(&output_file_path).expect("Could not open output file for reading");
        let found_log_entries = json::read_log_entries(&mut file_reader)
            .expect("Could not read output file as json log entries");

        assert!(found_log_entries.len() > 0);
        let expected_probe_ids: HashSet<_> = [probe_a_id, probe_b_id].iter().copied().collect();
        let built_in_event_ids: HashSet<_> = modality_probe::EventId::INTERNAL_EVENTS
            .iter()
            .map(|id| id.get_raw())
            .collect();
        for e in found_log_entries {
            assert_eq!(session_id, e.session_id);
            assert!(expected_probe_ids.contains(&e.probe_id));
            match e.data {
                LogEntryData::Event(event) => {
                    if e.probe_id == probe_a_id {
                        // Process A should only be writing about event foo or the probe internal events
                        assert!(
                            EventLogEntry::Event(event) == event_foo
                                || built_in_event_ids.contains(&event.get_raw())
                        );
                    } else if e.probe_id == probe_b_id {
                        // Process B should only be writing about event bar or the probe internals events
                        assert!(
                            EventLogEntry::Event(event) == event_bar
                                || built_in_event_ids.contains(&event.get_raw()),
                            "unexpected event for entry: {:?}",
                            e
                        );
                    }
                }
                LogEntryData::EventWithPayload(_, _) => (),
                LogEntryData::FrontierClock(lc) => {
                    if e.probe_id == probe_a_id {
                        // Process A should only know about itself, since it doesn't receive history from anyone else
                        assert_eq!(lc.id, probe_a_id);
                    } else {
                        // Process B should have clocks for both process's probe ids
                        assert!(expected_probe_ids.contains(&lc.id));
                    }
                }
                LogEntryData::TraceClock(lc) => {
                    if e.probe_id == probe_a_id {
                        assert_eq!(lc.id, probe_a_id);
                    } else {
                        assert!(expected_probe_ids.contains(&lc.id));
                    }
                }
                LogEntryData::WallClockTime(_) => (),
                LogEntryData::EventWithTime(_, _) => (),
                LogEntryData::EventWithPayloadWithTime(_, _, _) => (),
                LogEntryData::TraceClockWithTime(_, _) => (),
            }
        }
    }

    #[test]
    fn linear_pair_graph_with_payload() {
        let addrs = find_usable_addrs(1);
        let server_addr = addrs[0];
        let (shutdown_sender, shutdown_receiver) = ShutdownSignalSender::new(server_addr);
        let (server_state_sender, server_state_receiver) = crossbeam::bounded(0);
        let session_id = gen_session_id().into();
        let f = tempfile::NamedTempFile::new().expect("Could not make temp file");
        let output_file_path = PathBuf::from(f.path());
        let config = Config {
            addr: server_addr,
            session_id,
            output_file: output_file_path.clone(),
        };
        let h = thread::spawn(move || {
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(config.output_file)
                .expect("Could not open file for writing");
            let socket = UdpSocket::bind(config.addr).expect("Could not bind to server socket");
            server_state_sender
                .send(ServerState::Started)
                .expect("Could not send status update");
            start_receiving_from_socket(socket, config.session_id, &mut file, shutdown_receiver);
            let _ = server_state_sender.send(ServerState::Shutdown);
        });
        thread::yield_now();
        assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
        let mut net = proc_graph::Network::new();
        let probe_a_id = modality_probe::ProbeId::new(31).unwrap();
        let probe_b_id = modality_probe::ProbeId::new(41).unwrap();
        let foo_payload = 777;
        let foo_id = modality_probe::EventId::new(7).unwrap();
        let event_foo = EventLogEntry::EventWithPayload(foo_id, foo_payload);
        let bar_payload = 490;
        let bar_id = modality_probe::EventId::new(23).unwrap();
        let event_bar = EventLogEntry::EventWithPayload(bar_id, bar_payload);

        const NUM_MESSAGES_FROM_A: usize = 11;

        let (network_done_sender, network_done_receiver) = crossbeam::bounded(0);
        net.add_process(
            "a",
            vec!["b"],
            make_message_broadcaster_proc(
                "a",
                probe_a_id,
                NUM_MESSAGES_FROM_A,
                server_addr,
                Some(event_foo),
            ),
        );
        net.add_process(
            "b",
            vec![],
            make_message_sink_proc(
                probe_b_id,
                NUM_MESSAGES_FROM_A,
                SendLogReportEveryFewMessages {
                    n_messages: 3,
                    collector_addr: server_addr,
                },
                Some(event_bar),
                network_done_sender,
            ),
        );
        net.start();
        thread::yield_now();

        assert_eq!(Ok(()), network_done_receiver.recv());
        // Thanks, UDP
        std::thread::sleep(std::time::Duration::from_millis(200));
        shutdown_sender.shutdown();
        assert_eq!(Ok(ServerState::Shutdown), server_state_receiver.recv());

        h.join().expect("Couldn't join server handler thread");

        let mut file_reader =
            std::fs::File::open(&output_file_path).expect("Could not open output file for reading");
        let found_log_entries = json::read_log_entries(&mut file_reader)
            .expect("Could not read output file as json log entries");

        assert!(found_log_entries.len() > 0);
        let expected_probe_ids: HashSet<_> = [probe_a_id, probe_b_id].iter().copied().collect();
        for e in found_log_entries {
            assert_eq!(session_id, e.session_id);
            assert!(expected_probe_ids.contains(&e.probe_id));
            match e.data {
                LogEntryData::Event(_) => (),
                LogEntryData::EventWithPayload(event, payload) => {
                    if event == foo_id {
                        assert_eq!(EventLogEntry::EventWithPayload(event, payload), event_foo);
                    } else if event == bar_id {
                        assert_eq!(EventLogEntry::EventWithPayload(event, payload), event_bar);
                    } else if event != modality_probe::EventId::EVENT_PROBE_INITIALIZED {
                        // it's that the model implementation of
                        // EventId doesn't or out the marker bits on
                        // read.
                        panic!("got unexpected event: {:?}", event);
                    }
                }
                LogEntryData::FrontierClock(lc) => {
                    if e.probe_id == probe_a_id {
                        // Process A should only know about itself, since it doesn't receive history from anyone else
                        assert_eq!(lc.id, probe_a_id);
                    } else {
                        // Process B should have clocks for both process's probe ids
                        assert!(expected_probe_ids.contains(&lc.id));
                    }
                }
                LogEntryData::TraceClock(lc) => {
                    if e.probe_id == probe_a_id {
                        assert_eq!(lc.id, probe_a_id);
                    } else {
                        assert!(expected_probe_ids.contains(&lc.id));
                    }
                }
                LogEntryData::WallClockTime(_) => (),
                LogEntryData::EventWithTime(_, _) => (),
                LogEntryData::EventWithPayloadWithTime(_, _, _) => (),
                LogEntryData::TraceClockWithTime(_, _) => (),
            }
        }
    }

    fn make_message_broadcaster_proc(
        proc_name: &'static str,
        probe_id: modality_probe::ProbeId,
        n_messages: usize,
        collector_addr: SocketAddr,
        per_iteration_event: Option<EventLogEntry>,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |id_to_sender, _receiver| {
            let mut probe_storage = vec![MaybeUninit::new(0u8); PROBE_STORAGE_BYTES_SIZE];
            let mut probe = modality_probe::ModalityProbe::new_with_storage(
                &mut probe_storage,
                probe_id,
                NanosecondResolution::UNSPECIFIED,
                WallClockId::local_only(),
                RestartCounterProvider::NoRestartTracking,
            )
            .expect("Could not make probe");
            let mut causal_history_blob = vec![0u8; SNAPSHOT_BYTES_SIZE];
            for _ in 0..n_messages {
                match per_iteration_event {
                    Some(EventLogEntry::Event(e)) => probe.record_event(e),
                    Some(EventLogEntry::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }
                let causal_history_bytes = probe
                    .produce_snapshot_bytes(&mut causal_history_blob)
                    .expect("Could not write history to share with other in-system member");

                for destination in id_to_sender.values() {
                    let history_copy = Vec::from(&causal_history_blob[..causal_history_bytes]);
                    destination
                        .send((proc_name.to_string(), history_copy))
                        .expect("Could not send message to other process");
                }
            }

            let mut log_report_storage = vec![0u8; LOG_REPORT_BYTES_SIZE];
            let socket =
                UdpSocket::bind(OS_PICK_ADDR_HINT).expect("Could not bind to client socket");
            let log_report_bytes = probe
                .report(&mut log_report_storage)
                .expect("Could not write log report in broadcaster");
            if let Some(log_report_bytes) = log_report_bytes {
                socket
                    .send_to(
                        &log_report_storage[..log_report_bytes.get()],
                        collector_addr,
                    )
                    .expect("Could not send log report to server");
            }
        }
    }

    #[derive(Clone, Copy)]
    struct SendLogReportEveryFewMessages {
        n_messages: usize,
        collector_addr: SocketAddr,
    }

    fn make_message_relay_proc(
        proc_name: &'static str,
        probe_id: modality_probe::ProbeId,
        stop_relaying_after_receiving_n_messages: usize,
        send_log_report_every_n_messages: Option<SendLogReportEveryFewMessages>,
        per_iteration_event: Option<EventLogEntry>,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |id_to_sender, receiver| {
            let mut probe_storage = vec![MaybeUninit::new(0u8); PROBE_STORAGE_BYTES_SIZE];
            let mut probe = modality_probe::ModalityProbe::new_with_storage(
                &mut probe_storage,
                probe_id,
                NanosecondResolution::UNSPECIFIED,
                WallClockId::local_only(),
                RestartCounterProvider::NoRestartTracking,
            )
            .expect("Could not make probe");

            let socket =
                UdpSocket::bind(OS_PICK_ADDR_HINT).expect("Could not bind to client socket");
            let mut log_report_storage = vec![0u8; LOG_REPORT_BYTES_SIZE];
            let mut causal_history_blob = vec![0u8; SNAPSHOT_BYTES_SIZE];

            let mut messages_received = 0;
            loop {
                let (_msg_source, message) = match receiver.recv() {
                    Ok(m) => m,
                    Err(std::sync::mpsc::RecvError) => {
                        panic!("Received on a channel with no senders!")
                    }
                };
                match per_iteration_event {
                    Some(EventLogEntry::Event(e)) => probe.record_event(e),
                    Some(EventLogEntry::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }
                probe
                    .merge_snapshot_bytes(&message)
                    .expect("Could not merge in history");

                if messages_received > stop_relaying_after_receiving_n_messages {
                    continue;
                }
                let causal_history_bytes = probe
                    .produce_snapshot_bytes(&mut causal_history_blob)
                    .expect("Could not write history to share with other in-system member");

                for destination in id_to_sender.values() {
                    let history_copy = Vec::from(&causal_history_blob[..causal_history_bytes]);
                    destination
                        .send((proc_name.to_string(), history_copy))
                        .expect("Could not send message to other process");
                }
                if let Some(SendLogReportEveryFewMessages {
                    n_messages,
                    collector_addr,
                }) = send_log_report_every_n_messages
                {
                    if messages_received % n_messages == 0 {
                        let log_report_bytes = probe
                            .report(&mut log_report_storage)
                            .expect("Could not write log report in relayer");
                        if let Some(log_report_bytes) = log_report_bytes {
                            socket
                                .send_to(
                                    &log_report_storage[..log_report_bytes.get()],
                                    collector_addr,
                                )
                                .expect("Could not send log report to server");
                        }
                    }
                }
                messages_received += 1;
            }
        }
    }

    fn make_message_sink_proc(
        probe_id: modality_probe::ProbeId,
        stop_after_receiving_n_messages: usize,
        send_log_report_every_n_messages: SendLogReportEveryFewMessages,
        per_iteration_event: Option<EventLogEntry>,
        stopped_sender: crossbeam::Sender<()>,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |_id_to_sender, receiver| {
            let mut probe_storage = vec![MaybeUninit::new(0u8); PROBE_STORAGE_BYTES_SIZE];
            let mut probe = modality_probe::ModalityProbe::new_with_storage(
                &mut probe_storage,
                probe_id,
                NanosecondResolution::UNSPECIFIED,
                WallClockId::local_only(),
                RestartCounterProvider::NoRestartTracking,
            )
            .expect("Could not make probe");

            let socket =
                UdpSocket::bind(OS_PICK_ADDR_HINT).expect("Could not bind to client socket");
            let mut log_report_storage = vec![0u8; LOG_REPORT_BYTES_SIZE];

            let mut messages_received = 0;
            while messages_received < stop_after_receiving_n_messages {
                let (_msg_source, message) = match receiver.recv() {
                    Ok(m) => m,
                    Err(std::sync::mpsc::RecvError) => {
                        panic!("Received on a channel with no senders!")
                    }
                };
                probe
                    .merge_snapshot_bytes(&message)
                    .expect("Could not merge in history");
                match per_iteration_event {
                    Some(EventLogEntry::Event(e)) => probe.record_event(e),
                    Some(EventLogEntry::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }

                if messages_received % send_log_report_every_n_messages.n_messages == 0 {
                    let log_report_bytes = probe
                        .report(&mut log_report_storage)
                        .expect("Could not write log report in sink");
                    if let Some(log_report_bytes) = log_report_bytes {
                        socket
                            .send_to(
                                &log_report_storage[..log_report_bytes.get()],
                                send_log_report_every_n_messages.collector_addr,
                            )
                            .expect("Could not send log report to server");
                    }
                }
                messages_received += 1;
            }

            stopped_sender
                .send(())
                .expect("Could not inform outside world the process is done");
        }
    }
}
