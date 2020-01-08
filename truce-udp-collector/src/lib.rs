use std::io::{Write, Error as IoError};
use std::net::{SocketAddr, UdpSocket};
use truce_analysis::model::{SessionId, LogEntry, LogEntryData, LogEntryId};
use std::path::PathBuf;
use chrono::Utc;

#[derive(Debug, PartialEq)]
pub struct Config {
    pub addr: SocketAddr,
    pub session_id: SessionId,
    pub output_file: PathBuf
}
pub fn start_receiving(config: Config) -> Result<(), IoError> {
    let mut file = std::fs::OpenOptions::new().append(true).create(true).open(config.output_file)?;
    start_receiving_at_addr(config.addr, config.session_id, &mut file)
}

pub fn start_receiving_at_addr<W: Write>(addr: SocketAddr, session_id: SessionId, log_output_writer: &mut W) -> Result<(), IoError> {
    start_receiving_from_socket(UdpSocket::bind(addr)?, session_id, log_output_writer);
    Ok(())
}

pub fn start_receiving_from_socket<W: Write>(socket: UdpSocket, session_id: SessionId, log_output_writer: &mut W) {
    let addr = socket.local_addr().map(|a| a.to_string());
    let mut buf = vec![0u8; 1024 * 1024];
    let mut raw_log_entry_id: u64 = 0;
    let mut log_entries_buffer: Vec<LogEntry> = Vec::with_capacity(4096);
    loop {
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
        let tracer_id = (log_report.tracer_id as u32).into();
        let mut preceding_entry: Option<LogEntryId> = None;
        for segment in log_report.segments {
            for clock_bucket in segment.clock_buckets {
                let id = LogEntryId::from(raw_log_entry_id);
                log_entries_buffer.push(LogEntry {
                    session_id,
                    id: raw_log_entry_id.into(),
                    tracer_id,
                    data: LogEntryData::LogicalClock((clock_bucket.tracer_id as u32).into(), clock_bucket.count as u32),
                    preceding_entry,
                    receive_time
                });
                raw_log_entry_id += 1;
                preceding_entry = Some(id);
            }
            for event in segment.events {
                let id = LogEntryId::from(raw_log_entry_id);
                log_entries_buffer.push(LogEntry {
                    session_id,
                    id: raw_log_entry_id.into(),
                    tracer_id,
                    data: LogEntryData::Event((event as u32).into()),
                    preceding_entry,
                    receive_time
                });
                raw_log_entry_id += 1;
                preceding_entry = Some(id);
            }
        }
        if let Err(e) = truce_analysis::write_csv_log_entries(log_output_writer, &log_entries_buffer, false) {
            eprintln!("Error writing log entries: {}", e);
        }
    }
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

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        unimplemented!()
    }
}
