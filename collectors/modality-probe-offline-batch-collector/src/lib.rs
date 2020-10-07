#![deny(warnings)]

use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::{self, BufRead, Read, Write};
use std::mem;
use std::path::PathBuf;

use buf_redux::BufReader;
use chrono::Utc;
use log::{debug, warn};
use modality_probe::{wire::WireReport, ProbeId};
use modality_probe_collector_common::{
    self as common, json, Report, ReportLogEntry, SequenceNumber, SessionId,
};
use structopt::StructOpt;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, StructOpt)]
#[structopt(
    name = "modality-probe-offline-batch-collector",
    about = "Utility to convert modality-probe binary reports into log files"
)]
pub struct Opts {
    /// Read binary probe report data from a file (instead of stdin)
    #[structopt(short = "i", long, parse(from_os_str))]
    pub input_path: Option<PathBuf>,

    /// The session id to associate with the collected trace data
    #[structopt(short = "s", long, default_value = "0")]
    pub session_id: u32,

    /// The output file location, defaults to the current directory
    #[structopt(short = "o", long, parse(from_os_str))]
    pub output_file: Option<PathBuf>,
}

#[derive(Clone, Debug, Default)]
pub struct ReportMetrics {
    pub bytes_accumulated: u64,
    pub bytes_discarded: u64,
    pub reports_discarded: u64,
    pub probe_report_metrics: HashMap<ProbeId, ProbeReportMetrics>,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ProbeReportMetrics {
    pub num_reports: u64,
    pub missed_seq_nums: u64,
    pub last_seq_num: SequenceNumber,
}

impl Default for ProbeReportMetrics {
    fn default() -> Self {
        ProbeReportMetrics {
            num_reports: 0,
            missed_seq_nums: 0,
            last_seq_num: SequenceNumber(0),
        }
    }
}

impl ProbeReportMetrics {
    fn update(&mut self, report: &Report) {
        if self.num_reports != 0 && (report.seq_num.prev() != self.last_seq_num) {
            self.missed_seq_nums = self.missed_seq_nums.saturating_add(1);
        }
        self.num_reports = self.num_reports.saturating_add(1);
        self.last_seq_num = report.seq_num;
    }
}

#[derive(Debug)]
pub struct OfflineBatchCollector<'a, I: Read, O: Write + 'a> {
    fingerprint_len: usize,
    header_len: usize,
    log_entries_buffer: Vec<ReportLogEntry>,
    metrics: ReportMetrics,
    session_id: SessionId,
    eof_reached: bool,
    reader: BufReader<I>,
    log_output_writer: &'a mut O,
}

impl<'a, I: Read, O: Write> OfflineBatchCollector<'a, I, O> {
    pub fn new(session_id: SessionId, reader: I, log_output_writer: &'a mut O) -> Self {
        let fingerprint_len = mem::size_of_val(&WireReport::<&[u8]>::FINGERPRINT);
        OfflineBatchCollector {
            fingerprint_len,
            header_len: WireReport::<&[u8]>::header_len(),
            log_entries_buffer: Vec::with_capacity(4096),
            metrics: ReportMetrics::default(),
            session_id,
            eof_reached: false,
            reader: BufReader::with_capacity_ringbuf(8192, reader),
            log_output_writer,
        }
    }

    /// Run the collection loop, consuming until EOF or an error is encountered
    pub fn run(mut self) -> io::Result<ReportMetrics> {
        // Keep consuming until EOF or an error is encountered
        loop {
            // Check for earlier EOF detected
            if self.eof_reached {
                debug!("Input reached EOF, shutting down");
                break;
            }

            let (bytes, recv_time) = match self.reader.fill_buf() {
                Ok(b) => (b, Utc::now()),
                Err(e) => {
                    warn!("Encounter an input reader error {:?}", e);
                    return Err(e);
                }
            };

            if bytes.is_empty() {
                debug!("Input reached EOF, shutting down");
                break;
            }

            let buffer_len = bytes.len();
            let mut bytes_consumed = 0;
            let mut fingerprint_offset = None;
            let mut fingerprint_offsets_checked = 0;

            // Search for the fingerprint one byte at a time
            for idx in 0..buffer_len {
                let slice = &bytes[idx..];
                if slice.len() >= self.fingerprint_len {
                    fingerprint_offsets_checked += 1;
                    let r = WireReport::new_unchecked(&slice[..]);
                    if r.check_fingerprint().is_ok() {
                        fingerprint_offset = Some(idx);
                        debug!(
                            "Found fingerprint at offset {}",
                            self.metrics.bytes_accumulated + idx as u64
                        );
                        if idx != 0 {
                            // Fingerprint not found at the start of the buffer
                            let throwaway_start = self.metrics.bytes_accumulated;
                            let throwaway_end = self.metrics.bytes_accumulated + (idx as u64 - 1);
                            self.metrics.bytes_discarded = self
                                .metrics
                                .bytes_discarded
                                .saturating_add(throwaway_end - throwaway_start + 1);
                            warn!(
                                "Throwing away bytes {}..={} (size {}), offset to fingerprint",
                                throwaway_start,
                                throwaway_end,
                                throwaway_end - throwaway_start + 1,
                            );
                        }

                        break;
                    }
                }
            }

            match fingerprint_offset {
                None => {
                    // No fingerprint found in this chunk, throw away bytes we've considered,
                    // up to next possible/partial fingerprint
                    let bytes_thrown_away = if buffer_len < self.fingerprint_len {
                        let eof_expected = self.read_check_eof()?;
                        if eof_expected {
                            // No more data, throw away the remaining
                            buffer_len
                        } else {
                            // More data in the input buffer, try again
                            continue;
                        }
                    } else {
                        fingerprint_offsets_checked
                    };
                    let throwaway_start = self.metrics.bytes_accumulated;
                    let throwaway_end = self.metrics.bytes_accumulated + bytes_thrown_away as u64;
                    warn!(
                        "Throwing away bytes {}..={} (size {}), searching for fingerprint",
                        throwaway_start, throwaway_end, bytes_thrown_away,
                    );
                    self.metrics.bytes_discarded = self
                        .metrics
                        .bytes_discarded
                        .saturating_add(bytes_thrown_away as _);
                    bytes_consumed += bytes_thrown_away;
                }
                Some(fingerprint_offset) => {
                    bytes_consumed += fingerprint_offset;
                    let slice = &bytes[fingerprint_offset..];
                    let r = WireReport::new_unchecked(&slice[..]);
                    if r.check_len().is_ok() && r.check_payload_len().is_ok() {
                        let payload_len = r.payload_len();
                        let report_size = self.header_len + payload_len;
                        bytes_consumed += report_size;
                        debug!("Found report, size {} bytes", report_size);
                        let report_bytes = &r.into_inner()[..report_size];
                        match Report::try_from(report_bytes) {
                            Ok(log_report) => {
                                let metrics = self
                                    .metrics
                                    .probe_report_metrics
                                    .entry(log_report.probe_id)
                                    .or_default();
                                metrics.update(&log_report);
                                self.log_entries_buffer.clear();
                                common::add_log_report_to_entries(
                                    &log_report,
                                    self.session_id,
                                    recv_time,
                                    &mut self.log_entries_buffer,
                                );
                            }
                            Err(e) => {
                                self.metrics.reports_discarded =
                                    self.metrics.reports_discarded.saturating_add(1);
                                self.metrics.bytes_discarded = self
                                    .metrics
                                    .bytes_discarded
                                    .saturating_add(report_size as _);
                                warn!("{}, throwing away {} bytes", e, report_size);
                            }
                        }
                        if let Err(e) = json::write_log_entries(
                            &mut self.log_output_writer,
                            &self.log_entries_buffer,
                        ) {
                            warn!("Error writing log entries: {}", e);
                        }
                        self.log_output_writer.flush()?;
                    } else {
                        // Need more data to fullfill the report, check if any is available
                        // or if we're at the EOF
                        let eof_expected = self.read_check_eof()?;
                        if eof_expected {
                            // No more available, throw away the remaining
                            bytes_consumed += buffer_len;
                            self.metrics.bytes_discarded =
                                self.metrics.bytes_discarded.saturating_add(buffer_len as _);
                        }
                    }
                }
            }

            self.reader.consume(bytes_consumed);
            self.metrics.bytes_accumulated = self
                .metrics
                .bytes_accumulated
                .saturating_add(bytes_consumed as u64);

            debug!(
                "Consuming {} bytes from input buffer, total bytes accumulated {}",
                bytes_consumed, self.metrics.bytes_accumulated
            );
        }

        Ok(self.metrics)
    }

    fn read_check_eof(&mut self) -> io::Result<bool> {
        let bytes_read = self.reader.read_into_buf()?;
        self.eof_reached = bytes_read == 0;
        Ok(self.eof_reached)
    }
}
