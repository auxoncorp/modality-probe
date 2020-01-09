use chrono::{DateTime, Utc};
use std::io::{Error as IoError, Write};
use std::net::{SocketAddr, UdpSocket};
use std::path::PathBuf;
use std::sync::mpsc::Receiver;
use truce_analysis::model::{LogEntry, LogEntryData, LogEntryId, SessionId};

#[derive(Debug, PartialEq)]
pub struct Config {
    pub addr: SocketAddr,
    pub session_id: SessionId,
    pub output_file: PathBuf,
}

pub fn start_receiving(config: Config, shutdown_signal: Receiver<()>) -> Result<(), IoError> {
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
        shutdown_signal,
        needs_csv_headers,
    )
}

pub fn start_receiving_at_addr<W: Write>(
    addr: SocketAddr,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal: Receiver<()>,
    needs_csv_headers: bool,
) -> Result<(), IoError> {
    start_receiving_from_socket(
        UdpSocket::bind(addr)?,
        session_id,
        log_output_writer,
        shutdown_signal,
        needs_csv_headers,
    );
    Ok(())
}

pub fn start_receiving_from_socket<W: Write>(
    socket: UdpSocket,
    session_id: SessionId,
    log_output_writer: &mut W,
    shutdown_signal: Receiver<()>,
    mut needs_csv_headers: bool,
) {
    let addr = socket.local_addr().map(|a| a.to_string());
    let mut buf = vec![0u8; 1024 * 1024];
    let mut raw_log_entry_id: u64 = 0;
    let mut log_entries_buffer: Vec<LogEntry> = Vec::with_capacity(4096);
    loop {
        if let Ok(_) = shutdown_signal.try_recv() {
            return;
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
        let receive_time = Utc::now();
        // N.B. If we were feeling bottlenecked, hand off the read bytes to another thread
        // N.B. If we were feeling fancy, do said handoff by reading directly into a rotating preallocated
        // slot in a concurrent queue, ala LMAX Disruptor

        let message_bytes = &buf[..bytes_read];
        let log_report = match materialize_log_report(message_bytes) {
            Ok(r) => r,
            Err(_) => {
                eprintln!("Error parsing a message.");
                continue;
            }
        };

        // N.B. To avoid copies and allocation, skip materializing a log report
        // and instead directly create log entries. Probably wise to wait until the
        // log format settles down some before doing this.
        log_entries_buffer.clear();
        raw_log_entry_id = add_log_report_to_entries(
            &log_report,
            session_id,
            raw_log_entry_id,
            receive_time,
            &mut log_entries_buffer,
        );
        if let Err(e) = truce_analysis::write_csv_log_entries(
            log_output_writer,
            &log_entries_buffer,
            needs_csv_headers,
        ) {
            eprintln!("Error writing log entries: {}", e);
        } else {
            needs_csv_headers = false;
        }
        let _ = log_output_writer.flush();
    }
}

fn add_log_report_to_entries(
    log_report: &LogReport,
    session_id: SessionId,
    initial_log_entry_id: u64,
    receive_time: DateTime<Utc>,
    log_entries_buffer: &mut Vec<LogEntry>,
) -> u64 {
    let mut raw_log_entry_id = initial_log_entry_id;
    let tracer_id = (log_report.tracer_id as u32).into();
    let mut preceding_entry: Option<LogEntryId> = None;
    for segment in &log_report.segments {
        for clock_bucket in &segment.clock_buckets {
            let id = LogEntryId::from(raw_log_entry_id);
            log_entries_buffer.push(LogEntry {
                session_id,
                id: raw_log_entry_id.into(),
                tracer_id,
                data: LogEntryData::LogicalClock(
                    (clock_bucket.tracer_id as u32).into(),
                    clock_bucket.count as u32,
                ),
                preceding_entry,
                receive_time,
            });
            raw_log_entry_id += 1;
            preceding_entry = Some(id);
        }
        for event in &segment.events {
            let id = LogEntryId::from(raw_log_entry_id);
            log_entries_buffer.push(LogEntry {
                session_id,
                id: raw_log_entry_id.into(),
                tracer_id,
                data: LogEntryData::Event((*event as u32).into()),
                preceding_entry,
                receive_time,
            });
            raw_log_entry_id += 1;
            preceding_entry = Some(id);
        }
    }
    raw_log_entry_id
}

#[allow(dead_code)]
pub mod lcm {
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}

/// Easy mode use of the allocator to fully materialize the log report,
/// ignoring all the benefits of streamability.
fn materialize_log_report(bytes: &[u8]) -> Result<LogReport, ()> {
    let mut buffer_reader = rust_lcm_codec::BufferReader::new(bytes);
    let r = lcm::log_reporting::begin_log_report_read(&mut buffer_reader).map_err(|_| ())?;
    let (tracer_id, r) = r.read_tracer_id().map_err(|_| ())?;
    let mut flags = ErrorFlags {
        has_overflowed_log: false,
        has_overflowed_num_buckets: false,
    };
    let r = r
        .read_flags(|fr| {
            let (log_overflow, fr) = fr.read_has_overflowed_log()?;
            flags.has_overflowed_log = log_overflow;
            let (buckets_overflow, fr) = fr.read_has_overflowed_num_buckets()?;
            flags.has_overflowed_num_buckets = buckets_overflow;
            Ok(fr)
        })
        .map_err(|_| ())?;
    let mut segments = Vec::new();
    let (_n_segments, mut r) = r.read_n_segments().map_err(|_| ())?;
    for segment_item_reader in &mut r {
        let mut segment = LogSegment::default();
        segment_item_reader
            .read(|sr| {
                let (_n_clock_buckets, sr) = sr.read_n_clock_buckets()?;
                let (_n_events, mut sr) = sr.read_n_events()?;
                for clock_bucket_item_reader in &mut sr {
                    clock_bucket_item_reader.read(|cbr| {
                        let (id, cbr) = cbr.read_tracer_id()?;
                        let (count, cbr) = cbr.read_count()?;
                        segment.clock_buckets.push(ClockBucket {
                            tracer_id: id,
                            count,
                        });
                        Ok(cbr)
                    })?;
                }
                let mut sr = sr.done()?;
                for event_item_reader in &mut sr {
                    segment.events.push(event_item_reader.read()?);
                }
                Ok(sr.done()?)
            })
            .map_err(|_| ())?;
        segments.push(segment);
    }
    let _ = r.done().map_err(|_| ())?;
    Ok(LogReport {
        tracer_id,
        flags,
        segments,
    })
}

/// Literal materialization of the log_report LCM structure
/// with no semantic enrichment.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LogReport {
    tracer_id: i32,
    flags: ErrorFlags,
    segments: Vec<LogSegment>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ErrorFlags {
    has_overflowed_log: bool,
    has_overflowed_num_buckets: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LogSegment {
    clock_buckets: Vec<ClockBucket>,
    events: Vec<i32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClockBucket {
    tracer_id: i32,
    count: i32,
}

impl LogReport {
    #[cfg(test)]
    fn write_log_report_as_lcm(&self, destination: &mut [u8]) -> Result<usize, ()> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::log_reporting::begin_log_report_write(&mut buffer_writer).map_err(|_| ())?;
        let w = w.write_tracer_id(self.tracer_id).map_err(|_| ())?;
        let w = w
            .write_flags(|fw| {
                let fw = fw.write_has_overflowed_log(self.flags.has_overflowed_log)?;
                let fw =
                    fw.write_has_overflowed_num_buckets(self.flags.has_overflowed_num_buckets)?;
                Ok(fw)
            })
            .map_err(|_| ())?;

        let expected_n_segments = self.segments.len();
        let mut w = w
            .write_n_segments(expected_n_segments as i32)
            .map_err(|_| ())?;
        for (segment_item_writer, segment) in (&mut w).zip(&self.segments) {
            segment_item_writer
                .write(|sw| {
                    let sw = sw.write_n_clock_buckets(segment.clock_buckets.len() as i32)?;
                    let mut sw = sw.write_n_events(segment.events.len() as i32)?;
                    for (bucket_item_writer, bucket) in (&mut sw).zip(&segment.clock_buckets) {
                        bucket_item_writer.write(|bw| {
                            Ok(bw
                                .write_tracer_id(bucket.tracer_id)?
                                .write_count(bucket.count)?)
                        })?;
                    }
                    let mut sw = sw.done()?;
                    for (event_item_writer, event) in (&mut sw).zip(&segment.events) {
                        event_item_writer.write(*event)?;
                    }
                    Ok(sw.done()?)
                })
                .map_err(|_| ())?;
        }
        let _w = w.done().map_err(|_| ())?;
        Ok(buffer_writer.cursor())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::net::{Ipv4Addr, SocketAddrV4, TcpListener};
    use std::sync::atomic::{AtomicU16, Ordering};

    fn dummy_report(raw_main_tracer_id: i32) -> LogReport {
        LogReport {
            tracer_id: raw_main_tracer_id,
            flags: ErrorFlags {
                has_overflowed_log: false,
                has_overflowed_num_buckets: false,
            },
            segments: vec![
                LogSegment {
                    clock_buckets: vec![
                        ClockBucket {
                            tracer_id: 31,
                            count: 14,
                        },
                        ClockBucket {
                            tracer_id: 15,
                            count: 9,
                        },
                    ],
                    events: vec![2653],
                },
                LogSegment {
                    clock_buckets: vec![ClockBucket {
                        tracer_id: 271,
                        count: 1,
                    }],
                    events: vec![793, 2384],
                },
            ],
        }
    }

    fn report_and_matching_entries(
        raw_main_tracer_id: i32,
        session_id: SessionId,
        initial_entry_id: u64,
        receive_time: DateTime<Utc>,
    ) -> (LogReport, Vec<LogEntry>) {
        let main_tracer_id = (raw_main_tracer_id as u32).into();

        (
            dummy_report(raw_main_tracer_id),
            vec![
                LogEntry {
                    session_id,
                    id: initial_entry_id.into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::LogicalClock(31.into(), 14),
                    preceding_entry: None,
                    receive_time,
                },
                LogEntry {
                    session_id,
                    id: (initial_entry_id + 1).into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::LogicalClock(15.into(), 9),
                    preceding_entry: Some(initial_entry_id.into()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    id: (initial_entry_id + 2).into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::Event(2653.into()),
                    preceding_entry: Some((initial_entry_id + 1).into()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    id: (initial_entry_id + 3).into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::LogicalClock(271.into(), 1),
                    preceding_entry: Some((initial_entry_id + 2).into()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    id: (initial_entry_id + 4).into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::Event(793.into()),
                    preceding_entry: Some((initial_entry_id + 3).into()),
                    receive_time,
                },
                LogEntry {
                    session_id,
                    id: (initial_entry_id + 5).into(),
                    tracer_id: main_tracer_id,
                    data: LogEntryData::Event(2384.into()),
                    preceding_entry: Some((initial_entry_id + 4).into()),
                    receive_time,
                },
            ],
        )
    }

    #[test]
    fn log_report_to_entries() {
        let raw_main_tracer_id = 31;
        let session_id = 81.into();
        let initial_entry_id = 3;
        let receive_time = Utc::now();
        let (report, expected_entries) = report_and_matching_entries(
            raw_main_tracer_id,
            session_id,
            initial_entry_id,
            receive_time,
        );
        let mut entries = Vec::new();
        let out_id = add_log_report_to_entries(
            &report,
            session_id,
            initial_entry_id,
            receive_time,
            &mut entries,
        );
        assert_eq!(6, entries.len());
        assert_eq!(out_id - initial_entry_id, entries.len() as u64);
        assert_eq!(expected_entries, entries);
    }

    static STARTING_PORT: AtomicU16 = AtomicU16::new(11000);

    fn find_usable_addrs(limit: usize) -> Vec<SocketAddr> {
        let start_at = STARTING_PORT.load(Ordering::SeqCst);
        (start_at..start_at + 1_000)
            .filter_map(|port| {
                let addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), port));
                if TcpListener::bind(addr).is_ok() {
                    STARTING_PORT.store(port, Ordering::SeqCst);
                    Some(addr)
                } else {
                    None
                }
            })
            .take(limit)
            .collect()
    }

    #[test]
    fn minimal_round_trip() {
        let (shutdown_sender, shutdown_receiver) = std::sync::mpsc::channel();
        let (server_state_sender, server_state_receiver) = crossbeam::unbounded();
        #[derive(Copy, Clone, PartialEq)]
        enum ServerState {
            Started,
            Shutdown,
        }
        let addrs = find_usable_addrs(2);
        let server_addr = *addrs.first().unwrap();
        let session_id = 314.into();
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
            );
            let _ = server_state_sender.send(ServerState::Shutdown);
        });
        std::thread::yield_now();

        let log_report = dummy_report(31);
        if let ServerState::Started = server_state_receiver
            .recv()
            .expect("Could not get state update")
        {
            let mut lcm_log_report = [0u8; 1024];
            let lcm_bytes = log_report
                .write_log_report_as_lcm(&mut lcm_log_report)
                .expect("Could not write log report as lcm");
            let client_addr = addrs[1];
            let socket =
                UdpSocket::bind(client_addr).expect("Could not bind to socket for sending");
            socket
                .send_to(&lcm_log_report[..lcm_bytes], server_addr)
                .expect("Could not send lcm bytes");
            std::thread::sleep(std::time::Duration::from_millis(200));
            let _ = shutdown_sender.send(());
            let _ = socket.send_to(&[0], server_addr);
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
        let found_log_entries = truce_analysis::read_csv_log_entries(&mut file_reader)
            .expect("Could not read output file as csv log entries");
        let expected_entries: usize = log_report
            .segments
            .iter()
            .map(|s| s.events.len() + s.clock_buckets.len())
            .sum();
        assert_eq!(expected_entries, found_log_entries.len());
        let found_entry_ids: HashSet<_> = found_log_entries.iter().map(|e| e.id.0).collect();
        assert_eq!(
            expected_entries,
            found_entry_ids.len(),
            "All entries must have unique ids"
        );
        for (i, e) in found_log_entries.iter().enumerate() {
            assert_eq!(session_id, e.session_id);
            assert_eq!(log_report.tracer_id as u32, e.tracer_id.0);
            if i == 0 {
                assert!(e.preceding_entry.is_none());
            } else {
                assert!(e.preceding_entry.is_some());
                assert!(found_entry_ids.contains(&e.preceding_entry.unwrap().0));
            }
        }
        h.join().expect("Couldn't join handler thread");
    }
}
