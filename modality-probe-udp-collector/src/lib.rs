use chrono::{DateTime, Utc};
use modality_probe::compact_log::LogEvent;
use std::io::{Error as IoError, Write};
use std::net::{SocketAddr, UdpSocket};
use std::path::PathBuf;
use util::alloc_log_report::*;
use util::model::{LogEntry, LogEntryData, SegmentId, SessionId};

mod chunked;

use chunked::*;

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
    let needs_csv_headers =
        !config.output_file.exists() || config.output_file.metadata()?.len() == 0;
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(config.output_file)?;
    start_receiving_at_addr(
        config.addr,
        config.session_id,
        &mut file,
        shutdown_signal_receiver,
        needs_csv_headers,
    )
}

pub fn start_receiving_at_addr<W: Write>(
    addr: SocketAddr,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal_receiver: ShutdownSignalReceiver,
    needs_csv_headers: bool,
) -> Result<(), IoError> {
    start_receiving_from_socket(
        UdpSocket::bind(addr)?,
        session_id,
        log_output_writer,
        shutdown_signal_receiver,
        needs_csv_headers,
        ChunkHandlingConfig::default(),
    );
    Ok(())
}

pub fn start_receiving_from_socket<W: Write>(
    socket: UdpSocket,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal_receiver: ShutdownSignalReceiver,
    mut needs_csv_headers: bool,
    chunk_handling_config: ChunkHandlingConfig,
) {
    let addr = socket.local_addr().map(|a| a.to_string());
    let mut buf = vec![0u8; 1024 * 1024];
    let mut next_segment_id: u32 = 0;
    let mut chunk_handler = ChunkHandler::new(chunk_handling_config);
    let mut log_entries_buffer: Vec<LogEntry> = Vec::with_capacity(4096);
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

        if matches_chunk_fingerprint(&buf[..bytes_read]) {
            chunk_handler.add_incoming_chunk(
                &buf[..modality_probe::report::chunked::MAX_CHUNK_BYTES],
                receive_time,
            );
            let owned_reports = chunk_handler.materialize_completed_reports();
            for (owned_report, recv_time) in owned_reports {
                next_segment_id = add_owned_report_to_entries(
                    owned_report,
                    session_id,
                    next_segment_id.into(),
                    recv_time,
                    &mut log_entries_buffer,
                );
            }
            chunk_handler.remove_stale_reports();
        } else {
            match LogReport::try_from_bulk_bytes(&buf[..bytes_read]) {
                Ok(log_report) => {
                    next_segment_id = add_log_report_to_entries(
                        &log_report,
                        session_id,
                        next_segment_id.into(),
                        receive_time,
                        &mut log_entries_buffer,
                    );
                }
                Err(_) => {
                    eprintln!("Error parsing a message as a bulk report");
                    continue;
                }
            };
        }

        if let Err(e) =
            util::write_csv_log_entries(log_output_writer, &log_entries_buffer, needs_csv_headers)
        {
            eprintln!("Error writing log entries: {}", e);
        } else {
            needs_csv_headers = false;
        }
        let _ = log_output_writer.flush();
    }
}

/// Returns the smallest available segment id
fn add_log_report_to_entries(
    log_report: &LogReport,
    session_id: SessionId,
    initial_segment_id: SegmentId,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<LogEntry>,
) -> u32 {
    let mut next_segment_id = initial_segment_id.0;
    let probe_id = log_report.probe_id;
    for segment in &log_report.segments {
        let mut segment_index = 0;

        for clock_bucket in &segment.clocks {
            log_entries_buffer.push(LogEntry {
                session_id,
                segment_id: next_segment_id.into(),
                segment_index,
                probe_id,
                data: LogEntryData::LogicalClock(clock_bucket.id, clock_bucket.count),
                receive_time,
            });

            segment_index += 1;
        }

        for event in &segment.events {
            match event {
                LogEvent::Event(ev) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::Event(*ev),
                        receive_time,
                    });
                }
                LogEvent::EventWithPayload(ev, payload) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::EventWithPayload(*ev, *payload),
                        receive_time,
                    });
                }
            }

            segment_index += 1;
        }

        next_segment_id += 1;
    }

    next_segment_id
}

/// Returns the smallest available segment id
fn add_owned_report_to_entries(
    report: LogReport,
    session_id: SessionId,
    initial_segment_id: SegmentId,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<LogEntry>,
) -> u32 {
    let mut next_segment_id = initial_segment_id.0;
    let probe_id = report.probe_id;
    for segment in report.segments {
        let mut segment_index = 0;

        for clock_bucket in segment.clocks {
            log_entries_buffer.push(LogEntry {
                session_id,
                segment_id: next_segment_id.into(),
                segment_index,
                probe_id,
                data: LogEntryData::LogicalClock(clock_bucket.id, clock_bucket.count as u32),
                receive_time,
            });

            segment_index += 1;
        }

        for event in &segment.events {
            match event {
                modality_probe::compact_log::LogEvent::Event(ev) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::Event(*ev),
                        receive_time,
                    });
                }
                modality_probe::compact_log::LogEvent::EventWithPayload(ev, payload) => {
                    log_entries_buffer.push(LogEntry {
                        session_id,
                        segment_id: next_segment_id.into(),
                        segment_index,
                        probe_id,
                        data: LogEntryData::EventWithPayload(*ev, *payload),
                        receive_time,
                    });
                }
            }

            segment_index += 1;
        }

        next_segment_id += 1;
    }

    next_segment_id
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

    use lazy_static::*;

    use modality_probe::{BulkReporter, ChunkedReporter, LogicalClock, Probe};

    use super::*;

    fn dummy_report(raw_main_probe_id: u32) -> LogReport {
        LogReport {
            probe_id: raw_main_probe_id.try_into().unwrap(),
            segments: vec![
                OwnedLogSegment {
                    clocks: vec![
                        LogicalClock {
                            id: 31.try_into().unwrap(),
                            count: 14,
                        },
                        LogicalClock {
                            id: 15.try_into().unwrap(),
                            count: 9,
                        },
                    ],
                    events: vec![LogEvent::Event(2653.try_into().unwrap())],
                },
                OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: 271.try_into().unwrap(),
                        count: 1,
                    }],
                    events: vec![
                        LogEvent::Event(793.try_into().unwrap()),
                        LogEvent::Event(2384.try_into().unwrap()),
                    ],
                },
            ],
            extension_bytes: vec![],
        }
    }

    fn report_and_matching_entries(
        raw_main_probe_id: u32,
        session_id: SessionId,
        start_segment_id: util::model::SegmentId,
        receive_time: DateTime<Utc>,
    ) -> (LogReport, Vec<LogEntry>) {
        let main_probe_id = raw_main_probe_id.try_into().unwrap();

        (
            dummy_report(raw_main_probe_id),
            vec![
                LogEntry {
                    session_id,
                    segment_id: start_segment_id,
                    segment_index: 0,
                    probe_id: main_probe_id,
                    data: LogEntryData::LogicalClock(31.try_into().unwrap(), 14),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    segment_id: start_segment_id,
                    segment_index: 1,
                    probe_id: main_probe_id,
                    data: LogEntryData::LogicalClock(15.try_into().unwrap(), 9),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    segment_id: start_segment_id,
                    segment_index: 2,
                    probe_id: main_probe_id,
                    data: LogEntryData::Event(2653.try_into().unwrap()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    segment_id: (start_segment_id.0 + 1).into(),
                    segment_index: 0,
                    probe_id: main_probe_id,
                    data: LogEntryData::LogicalClock(271.try_into().unwrap(), 1),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    segment_id: (start_segment_id.0 + 1).into(),
                    segment_index: 1,
                    probe_id: main_probe_id,
                    data: LogEntryData::Event(793.try_into().unwrap()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    segment_id: (start_segment_id.0 + 1).into(),
                    segment_index: 2,
                    probe_id: main_probe_id,
                    data: LogEntryData::Event(2384.try_into().unwrap()),
                    receive_time,
                },
            ],
        )
    }

    #[test]
    fn log_report_to_entries() {
        let raw_main_probe_id = 31;
        let session_id = 81.into();
        let initial_segment_id = 3.into();
        let receive_time = Utc::now();
        let (report, expected_entries) = report_and_matching_entries(
            raw_main_probe_id,
            session_id,
            initial_segment_id,
            receive_time,
        );
        let mut entries = Vec::new();
        let out_segment_id = add_log_report_to_entries(
            &report,
            session_id,
            initial_segment_id,
            receive_time,
            &mut entries,
        );
        assert_eq!(6, entries.len());
        assert_eq!(out_segment_id - initial_segment_id.0, 2);
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
            start_receiving_from_socket(
                socket,
                config.session_id,
                &mut file,
                shutdown_receiver,
                true,
                ChunkHandlingConfig::default(),
            );
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
                .write_bulk_bytes(&mut lcm_log_report)
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
        let found_log_entries = util::read_csv_log_entries(&mut file_reader)
            .expect("Could not read output file as csv log entries");

        let expected_entries: usize = log_report
            .segments
            .iter()
            .map(|s| s.events.len() + s.clocks.len())
            .sum();
        assert_eq!(expected_entries, found_log_entries.len());

        let found_entry_ids: HashSet<_> = found_log_entries
            .iter()
            .map(|e| (e.session_id, e.segment_id, e.segment_index))
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
    const PROBE_STORAGE_BYTES_SIZE: usize = 256;
    const IN_SYSTEM_SNAPSHOT_BYTES_SIZE: usize = 256;
    const LOG_REPORT_BYTES_SIZE: usize = 512;

    trait HasEventId {
        fn get_id(&self) -> modality_probe::EventId;
        fn get_raw_id(&self) -> u32 {
            self.get_id().get_raw()
        }
    }
    impl HasEventId for LogEvent {
        fn get_id(&self) -> modality_probe::EventId {
            match self {
                LogEvent::Event(e) => *e,
                LogEvent::EventWithPayload(e, _) => *e,
            }
        }
    }

    #[test]
    fn linear_triple_inferred_unreporting_middleman_graph() {
        for use_chunked_reporting in &[true, false] {
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
                start_receiving_from_socket(
                    socket,
                    config.session_id,
                    &mut file,
                    shutdown_receiver,
                    true,
                    ChunkHandlingConfig::default(),
                );
                let _ = server_state_sender.send(ServerState::Shutdown);
            });
            thread::yield_now();
            assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
            let mut net = proc_graph::Network::new();
            let probe_a_id = modality_probe::ProbeId::new(131).unwrap();
            let probe_b_id = modality_probe::ProbeId::new(141).unwrap();
            let probe_c_id = modality_probe::ProbeId::new(159).unwrap();
            let event_foo = LogEvent::Event(modality_probe::EventId::new(7).unwrap());
            let event_bar = LogEvent::Event(modality_probe::EventId::new(23).unwrap());
            let event_baz = LogEvent::Event(modality_probe::EventId::new(29).unwrap());
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
                    *use_chunked_reporting,
                ),
            );
            net.add_process(
                "b",
                vec!["c"],
                make_message_relay_proc(
                    "b",
                    probe_b_id,
                    NUM_MESSAGES_FROM_A,
                    None,
                    Some(event_bar),
                    *use_chunked_reporting,
                ),
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
                    *use_chunked_reporting,
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

            let mut file_reader = std::fs::File::open(&output_file_path)
                .expect("Could not open output file for reading");
            let found_log_entries = util::read_csv_log_entries(&mut file_reader)
                .expect("Could not read output file as csv log entries");

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
                        if event.get_raw() == event_bar.get_raw_id() {
                            panic!("How the heck did bar get ove there?");
                        }
                        if e.probe_id.get_raw() == probe_a_id.get_raw() {
                            // Process A should only be writing about event foo or the probe internal events
                            assert!(
                                event.get_raw() == event_foo.get_raw_id()
                                    || built_in_event_ids.contains(&event)
                            );
                        } else if e.probe_id.get_raw() == probe_c_id.get_raw() {
                            // Process C should only be writing about event baz or the probe internals events
                            assert!(
                                event.get_raw() == event_baz.get_raw_id()
                                    || built_in_event_ids.contains(&event),
                                "unexpected event for entry: {:?}",
                                e
                            );
                        }
                    }
                    LogEntryData::EventWithPayload(_, _) => (),
                    LogEntryData::LogicalClock(tid, _count) => {
                        if e.probe_id == probe_a_id {
                            // Process A should only know about itself, since it doesn't receive history from anyone else
                            assert_eq!(tid, probe_a_id);
                        } else if e.probe_id == probe_c_id {
                            // Process C should have clocks for itself and its direct precursor, B
                            assert!(tid == probe_c_id || tid == probe_b_id);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn linear_pair_graph() {
        for use_chunked_reporting in &[true, false] {
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
                start_receiving_from_socket(
                    socket,
                    config.session_id,
                    &mut file,
                    shutdown_receiver,
                    true,
                    ChunkHandlingConfig::default(),
                );
                let _ = server_state_sender.send(ServerState::Shutdown);
            });
            thread::yield_now();
            assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
            let mut net = proc_graph::Network::new();
            let probe_a_id = modality_probe::ProbeId::new(31).unwrap();
            let probe_b_id = modality_probe::ProbeId::new(41).unwrap();
            let event_foo = LogEvent::Event(modality_probe::EventId::new(7).unwrap());
            let event_bar = LogEvent::Event(modality_probe::EventId::new(23).unwrap());
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
                    *use_chunked_reporting,
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
                    *use_chunked_reporting,
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

            let mut file_reader = std::fs::File::open(&output_file_path)
                .expect("Could not open output file for reading");
            let found_log_entries = util::read_csv_log_entries(&mut file_reader)
                .expect("Could not read output file as csv log entries");

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
                                event.get_raw() == event_foo.get_raw_id()
                                    || built_in_event_ids.contains(&event.get_raw())
                            );
                        } else if e.probe_id == probe_b_id {
                            // Process B should only be writing about event bar or the probe internals events
                            assert!(
                                event.get_raw() == event_bar.get_raw_id()
                                    || built_in_event_ids.contains(&event.get_raw()),
                                "unexpected event for entry: {:?}",
                                e
                            );
                        }
                    }
                    LogEntryData::EventWithPayload(_, _) => (),
                    LogEntryData::LogicalClock(tid, _count) => {
                        if e.probe_id == probe_a_id {
                            // Process A should only know about itself, since it doesn't receive history from anyone else
                            assert_eq!(tid, probe_a_id);
                        } else {
                            // Process B should have clocks for both process's probe ids
                            assert!(expected_probe_ids.contains(&tid));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn linear_pair_graph_with_payload() {
        for use_chunked_reporting in &[true, false] {
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
                start_receiving_from_socket(
                    socket,
                    config.session_id,
                    &mut file,
                    shutdown_receiver,
                    true,
                    ChunkHandlingConfig::default(),
                );
                let _ = server_state_sender.send(ServerState::Shutdown);
            });
            thread::yield_now();
            assert_eq!(Ok(ServerState::Started), server_state_receiver.recv());
            let mut net = proc_graph::Network::new();
            let probe_a_id = modality_probe::ProbeId::new(31).unwrap();
            let probe_b_id = modality_probe::ProbeId::new(41).unwrap();
            let foo_payload = 777;
            let event_foo =
                LogEvent::EventWithPayload(modality_probe::EventId::new(7).unwrap(), foo_payload);
            let bar_payload = 490;
            let event_bar =
                LogEvent::EventWithPayload(modality_probe::EventId::new(23).unwrap(), bar_payload);

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
                    *use_chunked_reporting,
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
                    *use_chunked_reporting,
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

            let mut file_reader = std::fs::File::open(&output_file_path)
                .expect("Could not open output file for reading");
            let found_log_entries = util::read_csv_log_entries(&mut file_reader)
                .expect("Could not read output file as csv log entries");

            assert!(found_log_entries.len() > 0);
            let expected_probe_ids: HashSet<_> = [probe_a_id, probe_b_id].iter().copied().collect();
            for e in found_log_entries {
                assert_eq!(session_id, e.session_id);
                assert!(expected_probe_ids.contains(&e.probe_id));
                match e.data {
                    LogEntryData::Event(_) => (),
                    LogEntryData::EventWithPayload(event, payload) => {
                        if event == event_foo.get_id() {
                            assert_eq!(foo_payload, payload);
                        } else if event == event_bar.get_id() {
                            assert_eq!(bar_payload, payload);
                        } else {
                            // it's that the model implementation of
                            // EventId doesn't or out the marker bits on
                            // read.
                            panic!("got unexpected event: {:?}", event);
                        }
                    }
                    LogEntryData::LogicalClock(tid, _count) => {
                        if e.probe_id == probe_a_id {
                            // Process A should only know about itself, since it doesn't receive history from anyone else
                            assert_eq!(tid, probe_a_id);
                        } else {
                            // Process B should have clocks for both process's probe ids
                            assert!(expected_probe_ids.contains(&tid));
                        }
                    }
                }
            }
        }
    }

    fn make_message_broadcaster_proc(
        proc_name: &'static str,
        probe_id: modality_probe::ProbeId,
        n_messages: usize,
        collector_addr: SocketAddr,
        per_iteration_event: Option<LogEvent>,
        use_chunked_reporting: bool,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |id_to_sender, _receiver| {
            let mut probe_storage = vec![0u8; PROBE_STORAGE_BYTES_SIZE];
            let mut probe =
                modality_probe::ModalityProbe::new_with_storage(&mut probe_storage, probe_id)
                    .expect("Could not make probe");
            let mut causal_history_blob = vec![0u8; IN_SYSTEM_SNAPSHOT_BYTES_SIZE];
            for _ in 0..n_messages {
                match per_iteration_event {
                    Some(LogEvent::Event(e)) => probe.record_event(e),
                    Some(LogEvent::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }
                let causal_history_bytes = probe
                    .distribute_snapshot(&mut causal_history_blob)
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
            if use_chunked_reporting {
                let token = probe
                    .start_chunked_report()
                    .expect("Could not start chunked report");
                loop {
                    let log_report_bytes = probe
                        .write_next_report_chunk(&token, &mut log_report_storage)
                        .expect("Could not write report chunk");
                    if log_report_bytes == 0 {
                        break;
                    }
                    socket
                        .send_to(&log_report_storage[..log_report_bytes], collector_addr)
                        .expect("Could not send log report to server");
                }
                probe
                    .finish_chunked_report(token)
                    .expect("Could not finish chunked report");
            } else {
                let log_report_bytes = probe
                    .report(&mut log_report_storage)
                    .expect("Could not write log report in broadcaster");
                socket
                    .send_to(&log_report_storage[..log_report_bytes], collector_addr)
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
        per_iteration_event: Option<LogEvent>,
        use_chunked_reporting: bool,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |id_to_sender, receiver| {
            let mut probe_storage = vec![0u8; PROBE_STORAGE_BYTES_SIZE];
            let mut probe =
                modality_probe::ModalityProbe::new_with_storage(&mut probe_storage, probe_id)
                    .expect("Could not make probe");

            let socket =
                UdpSocket::bind(OS_PICK_ADDR_HINT).expect("Could not bind to client socket");
            let mut log_report_storage = vec![0u8; LOG_REPORT_BYTES_SIZE];

            let mut causal_history_blob = vec![0u8; IN_SYSTEM_SNAPSHOT_BYTES_SIZE];
            let mut messages_received = 0;
            loop {
                let (_msg_source, message) = match receiver.recv() {
                    Ok(m) => m,
                    Err(std::sync::mpsc::RecvError) => {
                        panic!("Received on a channel with no senders!")
                    }
                };
                match per_iteration_event {
                    Some(LogEvent::Event(e)) => probe.record_event(e),
                    Some(LogEvent::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }
                probe
                    .merge_snapshot(&message)
                    .expect("Could not merge in history");

                if messages_received > stop_relaying_after_receiving_n_messages {
                    continue;
                }
                let causal_history_bytes = probe
                    .distribute_snapshot(&mut causal_history_blob)
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
                        if use_chunked_reporting {
                            let token = probe
                                .start_chunked_report()
                                .expect("Could not start chunked report");
                            loop {
                                let log_report_bytes = probe
                                    .write_next_report_chunk(&token, &mut log_report_storage)
                                    .expect("Could not write report chunk");
                                if log_report_bytes == 0 {
                                    break;
                                }
                                socket
                                    .send_to(
                                        &log_report_storage[..log_report_bytes],
                                        collector_addr,
                                    )
                                    .expect("Could not send log report to server");
                            }
                            probe
                                .finish_chunked_report(token)
                                .expect("Could not finish chunked report");
                        } else {
                            let log_report_bytes = probe
                                .report(&mut log_report_storage)
                                .expect("Could not write log report in relayer");
                            socket
                                .send_to(&log_report_storage[..log_report_bytes], collector_addr)
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
        per_iteration_event: Option<LogEvent>,
        stopped_sender: crossbeam::Sender<()>,
        use_chunked_reporting: bool,
    ) -> impl Fn(
        HashMap<String, std::sync::mpsc::Sender<(String, Vec<u8>)>>,
        std::sync::mpsc::Receiver<(String, Vec<u8>)>,
    ) + Send
           + 'static {
        move |_id_to_sender, receiver| {
            let mut probe_storage = vec![0u8; PROBE_STORAGE_BYTES_SIZE];
            let mut probe =
                modality_probe::ModalityProbe::new_with_storage(&mut probe_storage, probe_id)
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
                    .merge_snapshot(&message)
                    .expect("Could not merge in history");
                match per_iteration_event {
                    Some(LogEvent::Event(e)) => probe.record_event(e),
                    Some(LogEvent::EventWithPayload(e, payload)) => {
                        probe.record_event_with_payload(e, payload)
                    }
                    _ => (),
                }

                if messages_received % send_log_report_every_n_messages.n_messages == 0 {
                    if use_chunked_reporting {
                        let token = probe
                            .start_chunked_report()
                            .expect("Could not start chunked report");
                        loop {
                            let log_report_bytes = probe
                                .write_next_report_chunk(&token, &mut log_report_storage)
                                .expect("Could not write report chunk");
                            if log_report_bytes == 0 {
                                break;
                            }
                            socket
                                .send_to(
                                    &log_report_storage[..log_report_bytes],
                                    send_log_report_every_n_messages.collector_addr,
                                )
                                .expect("Could not send log report to server");
                        }
                        probe
                            .finish_chunked_report(token)
                            .expect("Could not finish chunked report");
                    } else {
                        let log_report_bytes = probe
                            .report(&mut log_report_storage)
                            .expect("Could not write log report in sink");
                        socket
                            .send_to(
                                &log_report_storage[..log_report_bytes],
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
