use chrono::Utc;
use std::cell::RefCell;
use std::fs::File;
use std::mem::size_of;
use std::net::SocketAddrV4;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::mpsc::Receiver;
use std::thread::sleep;
use std::time::Duration;

use err_derive::Error;
use field_offset::offset_of;
use probe_rs::{MemoryInterface, Session};

use modality_probe::log::LogEntry;
use modality_probe::{
    DynamicHistory, EventId, LogicalClock, ModalityProbe, OrdClock, OverwritePriorityLevel,
    ProbeEpoch, ProbeId, ProbeTicks,
};
use modality_probe_collector_common::{
    add_log_report_to_entries, csv::write_log_entries, Report, ReportLogEntry, SessionId,
};
use race_buffer::async_reader::{RaceReader, Snapper};
use race_buffer::{RaceBuffer, SeqNum, WholeEntry};

// Offset of pointer to DynamicHistory in ModalityProbe struct, which is located in modality-probe/src/lib.rs
fn history_ptr_offset() -> u32 {
    offset_of!(ModalityProbe => history).get_byte_offset() as u32
}

// Address offsets of each needed field of the DynamicHistory struct, which is located in modality-probe/src/history.rs
fn overwrite_priority_offset() -> u32 {
    offset_of!(DynamicHistory => overwrite_priority).get_byte_offset() as u32
}

fn probe_id_offset() -> u32 {
    offset_of!(DynamicHistory => probe_id).get_byte_offset() as u32
}

fn write_seqn_high_offset() -> u32 {
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => write_seqn: SeqNum => high)
        .get_byte_offset() as u32
}

fn write_seqn_low_offset() -> u32 {
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => write_seqn: SeqNum => low)
        .get_byte_offset() as u32
}

fn overwrite_seqn_high_offset() -> u32 {
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => overwrite_seqn: SeqNum => high)
        .get_byte_offset() as u32
}

fn overwrite_seqn_low_offset() -> u32 {
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => overwrite_seqn: SeqNum => low)
        .get_byte_offset() as u32
}

fn log_storage_addr_offset() -> u32 {
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => storage).get_byte_offset() as u32
}

fn log_storage_cap_offset() -> u32 {
    // Assume storage addr is a u32
    log_storage_addr_offset() + size_of::<u32>() as u32
}

/// Configuration for running collector
#[derive(Debug, PartialEq)]
pub struct Config {
    pub session_id: SessionId,
    pub big_endian: bool,
    pub attach_target: Option<String>,
    pub gdb_addr: Option<SocketAddrV4>,
    pub interval: Duration,
    pub output_path: PathBuf,
    pub probe_addrs: Vec<ProbeAddr>,
}

/// Struct representing a probe address, either the address of the probe itself or of
/// a pointer to the probe
#[derive(Debug, PartialEq)]
pub enum ProbeAddr {
    Addr(u32),
    PtrAddr(u32),
}

#[derive(Debug, Error)]
pub enum DebugCollectorError {
    #[error(display = "Error reading from/writing to target")]
    TargetError,
    #[error(display = "Invalid probe id read from device")]
    ProbeIdError,
    #[error(display = "Error processing the report's log")]
    LogProcessingError,
    #[error(display = "Error serializing the report")]
    ReportSerializationError,
    #[error(display = "Error using output file")]
    FileError,
}

/// Trait used to specify backend used to access device memory
pub trait MemoryAccessor {
    fn read_32(&mut self, addr: u32) -> Result<u32, DebugCollectorError>;
    fn write_32(&mut self, addr: u32, data: u32) -> Result<(), DebugCollectorError>;
}

/// MemoryAccessor that uses probe-rs to access device memory
struct ProbeRsReader(Session);

impl MemoryAccessor for ProbeRsReader {
    fn read_32(&mut self, addr: u32) -> Result<u32, DebugCollectorError> {
        let mut core = self
            .0
            .core(0)
            .map_err(|_e| DebugCollectorError::TargetError)?;
        core.read_word_32(addr)
            .map_err(|_e| DebugCollectorError::TargetError)
    }
    fn write_32(&mut self, addr: u32, data: u32) -> Result<(), DebugCollectorError> {
        let mut core = self
            .0
            .core(0)
            .map_err(|_e| DebugCollectorError::TargetError)?;
        core.write_word_32(addr, data)
            .map_err(|_e| DebugCollectorError::TargetError)
    }
}

/// Struct used to take snapshots of RaceBuffer on device
struct MemorySnapper {
    /// Reader used to read device memory
    mem_accessor: Rc<RefCell<dyn MemoryAccessor>>,
    /// Address of RaceBuffer backing storage
    storage_addr: u32,
    /// Address of RaceBuffer write sequence number high word
    write_seqn_high_addr: u32,
    /// Address of RaceBuffer write sequence number low word
    write_seqn_low_addr: u32,
    /// Address of RaceBuffer write sequence number high word
    overwrite_seqn_high_addr: u32,
    /// Address of RaceBuffer write sequence number low word
    overwrite_seqn_low_addr: u32,
}

impl Snapper<LogEntry> for MemorySnapper {
    type Error = DebugCollectorError;

    fn snap_write_seqn_high(&self) -> Result<u32, DebugCollectorError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.write_seqn_high_addr)
    }

    fn snap_write_seqn_low(&self) -> Result<u32, DebugCollectorError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.write_seqn_low_addr)
    }

    fn snap_overwrite_seqn_high(&self) -> Result<u32, DebugCollectorError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.overwrite_seqn_high_addr)
    }

    fn snap_overwrite_seqn_low(&self) -> Result<u32, DebugCollectorError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.overwrite_seqn_low_addr)
    }

    fn snap_storage(&self, index: usize) -> Result<LogEntry, DebugCollectorError> {
        let raw: u32 = self
            .mem_accessor
            .borrow_mut()
            .read_32(self.storage_addr + (size_of::<LogEntry>() * index) as u32)?;
        // Safe because entry is already in memory as a valid LogEntry
        Ok(unsafe { LogEntry::new_unchecked(raw) })
    }
}

/// Used to write to probe's "overwrite_priority" field
struct PriorityWriter {
    /// Memory accessor used to write to device memoryt
    mem_accessor: Rc<RefCell<dyn MemoryAccessor>>,
    /// Address of priority field
    priority_field_addr: u32,
}

impl PriorityWriter {
    fn write(&mut self, level: OverwritePriorityLevel) -> Result<(), DebugCollectorError> {
        self.mem_accessor
            .borrow_mut()
            .write_32(self.priority_field_addr, level.0)
    }
}

/// Log collector for a single probe
pub struct Collector {
    /// Sequence number of next report
    seq_num: u64,
    /// Reader used to read the probe's RaceBuffer
    reader: RaceReader<LogEntry, MemorySnapper>,
    /// Allocated buffer for reading the log into
    rbuf: Vec<WholeEntry<LogEntry>>,
    /// Processed clocks backing storage
    clocks: Vec<LogicalClock>,
    /// Used to write to the probe's "overwrite_priority" field
    priority_writer: PriorityWriter,
}

impl Collector {
    /// Initialize collector by reading probe information
    pub fn initialize(
        probe_addr: &ProbeAddr,
        mem_accessor: Rc<RefCell<dyn MemoryAccessor>>,
    ) -> Result<Self, DebugCollectorError> {
        let addr = match *probe_addr {
            ProbeAddr::Addr(addr) => addr,
            // Read storage address from pointer
            ProbeAddr::PtrAddr(addr) => mem_accessor.borrow_mut().read_32(addr)?,
        };
        let mut mem_accessor_borrowed = mem_accessor.borrow_mut();
        // Get address of DynamicHistory
        let hist_addr = mem_accessor_borrowed.read_32(addr + history_ptr_offset())?;
        // Read DynamicHistory fields
        let id_raw = mem_accessor_borrowed.read_32(hist_addr + probe_id_offset())?;
        let id = ProbeId::new(id_raw).ok_or_else(|| DebugCollectorError::ProbeIdError)?;
        let buf_addr = mem_accessor_borrowed.read_32(hist_addr + log_storage_addr_offset())?;
        let buf_cap = mem_accessor_borrowed.read_32(hist_addr + log_storage_cap_offset())? as usize;
        let write_seqn_high_addr = hist_addr + write_seqn_high_offset();
        let write_seqn_low_addr = hist_addr + write_seqn_low_offset();
        let overwrite_seqn_high_addr = hist_addr + overwrite_seqn_high_offset();
        let overwrite_seqn_low_addr = hist_addr + overwrite_seqn_low_offset();
        let priority_field_addr = hist_addr + overwrite_priority_offset();
        drop(mem_accessor_borrowed);

        let priority_mem_accessor = mem_accessor.clone();
        let mut clocks = Vec::new();
        // Merge self clock set to 0
        Self::merge_clock(
            &mut clocks,
            LogicalClock {
                id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            },
        );
        Ok(Self {
            seq_num: 0,
            reader: RaceReader::new(
                MemorySnapper {
                    mem_accessor,
                    storage_addr: buf_addr,
                    write_seqn_high_addr,
                    write_seqn_low_addr,
                    overwrite_seqn_high_addr,
                    overwrite_seqn_low_addr,
                },
                buf_cap,
            ),
            rbuf: Vec::new(),
            clocks,
            priority_writer: PriorityWriter {
                mem_accessor: priority_mem_accessor,
                priority_field_addr,
            },
        })
    }

    /// Collect all new logs, return a report
    pub fn collect_report(&mut self) -> Result<Report, DebugCollectorError> {
        let num_missed = self.reader.read(&mut self.rbuf)?;
        // Possibly add entries missed event
        if num_missed > 0 {
            let num_missed_rounded = u64::max(num_missed, u32::MAX as u64) as u32;
            let (ev, payload) =
                LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, num_missed_rounded);
            self.rbuf.insert(0, WholeEntry::Double(ev, payload));
        }

        // Keep a copy of the clocks before this report which will be used as frontier clocks
        let report_clocks = self.clocks.clone();

        // Merge clocks from this report
        for entry in self.rbuf.iter() {
            if let WholeEntry::Double(first, second) = entry {
                if first.has_clock_bit_set() {
                    let id = ProbeId::new(first.interpret_as_logical_clock_probe_id())
                        .ok_or_else(|| DebugCollectorError::LogProcessingError)?;
                    let (epoch, ticks) = modality_probe::unpack_clock_word(second.raw());
                    Self::merge_clock(&mut self.clocks, LogicalClock { id, epoch, ticks })
                }
            }
        }

        let report =
            Report::try_from_log(self.clocks[0], self.seq_num, report_clocks, &self.rbuf[..])
                .and_then(|report| {
                    self.seq_num += 1;
                    Ok(report)
                })
                .map_err(|_e| DebugCollectorError::ReportSerializationError);
        self.rbuf.clear();
        report
    }

    fn merge_clock(clocks: &mut Vec<LogicalClock>, ext_clock: LogicalClock) {
        let mut existed = false;
        for c in clocks.iter_mut() {
            if c.id == ext_clock.id {
                if OrdClock(ext_clock.epoch, ext_clock.ticks) > OrdClock(c.epoch, c.ticks) {
                    c.epoch = ext_clock.epoch;
                    c.ticks = ext_clock.ticks;
                }
                existed = true;
            }
        }
        if !existed {
            clocks.push(ext_clock);
        }
    }

    /// Write to "write priority" field in probe
    pub fn set_overwrite_priority(
        &mut self,
        level: OverwritePriorityLevel,
    ) -> Result<(), DebugCollectorError> {
        self.priority_writer.write(level)
    }
}

/// Open memory reader based on config
fn open_memory_reader(c: &Config) -> Result<Rc<RefCell<dyn MemoryAccessor>>, DebugCollectorError> {
    Ok(Rc::new(RefCell::new(match c.attach_target.as_ref() {
        Some(target) => {
            let session =
                Session::auto_attach(target).map_err(|_e| DebugCollectorError::TargetError)?;
            ProbeRsReader(session)
        }
        // No probe rs target implies use of gdb, which is not implemented yet
        None => unimplemented!(),
    })))
}

/// Initialize collectors of each probe based on config
fn initialize_collectors(
    c: &Config,
    mem_accessor: Rc<RefCell<dyn MemoryAccessor>>,
) -> Result<Vec<Collector>, DebugCollectorError> {
    let mut collectors = Vec::new();
    for probe_addr in c.probe_addrs.iter() {
        collectors.push(Collector::initialize(probe_addr, mem_accessor.clone())?);
    }
    Ok(collectors)
}

/// Write report to given file
fn report_to_file(
    out: &mut File,
    report: Report,
    session_id: SessionId,
    include_header_row: bool,
) -> Result<(), DebugCollectorError> {
    let mut entries: Vec<ReportLogEntry> = Vec::new();

    add_log_report_to_entries(&report, session_id, Utc::now(), &mut entries);
    write_log_entries(out, &entries, include_header_row)
        .map_err(|_e| DebugCollectorError::FileError)
}

/// Run debug collector with given config
pub fn run(c: &Config, shutdown_receiver: Receiver<()>) -> Result<(), DebugCollectorError> {
    let mem_accessor = open_memory_reader(c)?;
    let mut collectors = initialize_collectors(c, mem_accessor)?;

    let mut needs_csv_headers = !c.output_path.exists()
        || c.output_path
            .metadata()
            .map_err(|_e| DebugCollectorError::FileError)?
            .len()
            == 0;
    let mut out = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&c.output_path)
        .map_err(|_e| DebugCollectorError::FileError)?;

    loop {
        if shutdown_receiver.try_recv().is_ok() {
            break;
        }
        for collector in &mut collectors {
            let report = collector.collect_report()?;
            report_to_file(&mut out, report, c.session_id, needs_csv_headers)?;
            needs_csv_headers = false;
        }
        sleep(c.interval);
    }
    Ok(())
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use maplit::hashmap;
    use std::collections::HashMap;
    use std::convert::TryInto;

    use modality_probe::EventId;
    use modality_probe_collector_common::EventLogEntry;

    struct HashMapMemAccessor(HashMap<u32, u32>);

    impl HashMapMemAccessor {
        const PROBE_PTR_ADDR: u32 = 0x0;
        const PROBE_ADDR: u32 = 0x4;
        const HIST_ADDR: u32 = 0x8;
        const STORAGE_ADDR: u32 = 0x200;

        fn new(
            probe_id: ProbeId,
            write_seqn: u32,
            overwrite_seqn: u32,
            buf_contents: &Vec<LogEntry>,
        ) -> Self {
            let map = hashmap! {
                Self::PROBE_PTR_ADDR => Self::PROBE_ADDR,
                Self::PROBE_ADDR + history_ptr_offset() => Self::HIST_ADDR,
                Self::HIST_ADDR + probe_id_offset() => probe_id.get().into(),
                Self::HIST_ADDR + log_storage_addr_offset() => Self::STORAGE_ADDR,
                Self::HIST_ADDR + log_storage_cap_offset() => buf_contents.len() as u32,
                Self::HIST_ADDR + write_seqn_offset() => write_seqn,
                Self::HIST_ADDR + overwrite_seqn_offset() => overwrite_seqn
            };
            let mut reader = HashMapMemAccessor(map);
            reader.overwrite_buffer(&buf_contents);
            reader
        }

        fn overwrite_buffer(&mut self, buf_contents: &Vec<LogEntry>) {
            for (index, entry) in buf_contents.iter().enumerate() {
                self.0
                    .insert(Self::STORAGE_ADDR + 4 * (index as u32), entry.raw());
            }
        }

        fn set_write_seqn(&mut self, new_write_seqn: u32) {
            self.0
                .insert(Self::HIST_ADDR + write_seqn_offset(), new_write_seqn);
        }

        fn set_overwrite_seqn(&mut self, new_overwrite_seqn: u32) {
            self.0.insert(
                Self::HIST_ADDR + overwrite_seqn_offset(),
                new_overwrite_seqn,
            );
        }
    }

    impl MemoryAccessor for HashMapMemAccessor {
        fn read_32(&mut self, addr: u32) -> DynResult<u32> {
            Ok(*self.0.get(&addr).unwrap())
        }

        fn write_32(&mut self, _: u32, _: u32) -> DynResult<()> {
            unimplemented!()
        }
    }

    fn lc(probe_id: u32, epoch: u16, ticks: u16) -> LogicalClock {
        LogicalClock {
            id: probe_id.try_into().unwrap(),
            epoch: epoch.into(),
            ticks: ticks.into(),
        }
    }

    fn ev(id: u32) -> EventId {
        EventId::new(id).unwrap()
    }

    #[test]
    fn initialization_and_retrieval() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            4,
            4,
            &mut vec![
                LogEntry::clock(lc(pid_raw, 0, 1)).0,
                LogEntry::clock(lc(pid_raw, 0, 1)).1,
                LogEntry::event(ev(3)),
                LogEntry::event(ev(4)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let mut rbuf = Vec::new();
        collector.retrieve_logs(&mut rbuf).unwrap();
        assert_eq!(
            &rbuf[..],
            &mut vec![
                PossiblyMissed::Entry(LogEntry::clock(lc(pid_raw, 0, 1)).0),
                PossiblyMissed::Entry(LogEntry::clock(lc(pid_raw, 0, 1)).1),
                PossiblyMissed::Entry(LogEntry::event(EventId::new(3).unwrap())),
                PossiblyMissed::Entry(LogEntry::event(EventId::new(4).unwrap())),
            ][..]
        )
    }

    /// Create simple report
    #[test]
    fn basic_collection() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            4,
            0,
            &mut vec![
                LogEntry::clock(lc(pid_raw, 0, 1)).0,
                LogEntry::clock(lc(pid_raw, 0, 1)).1,
                LogEntry::event(ev(3)),
                LogEntry::event(ev(4)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();

        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4))
                ],
            }
        )
    }

    /// Check that local clock is implied at start
    #[test]
    fn no_clocks_available() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            4,
            0,
            &mut vec![
                LogEntry::event(ev(1)),
                LogEntry::event(ev(2)),
                LogEntry::event(ev(3)),
                LogEntry::event(ev(4)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4))
                ],
            }
        )
    }

    /// Put clocks before missed at start
    #[test]
    fn missed_at_start() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            6,
            2,
            &mut vec![
                LogEntry::event(ev(5)),
                LogEntry::event(ev(6)),
                LogEntry::event(ev(3)),
                LogEntry::event(ev(4)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();

        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithPayload(EventId::EVENT_LOG_ITEMS_MISSED, 2),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6))
                ],
            }
        )
    }

    /// Imply clocks at start of read if not present
    #[test]
    fn imply_multiple_clocks() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let other_id_raw = 2;
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            8,
            0,
            &mut vec![
                LogEntry::clock(lc(pid_raw, 0, 1)).0,
                LogEntry::clock(lc(pid_raw, 0, 1)).1,
                LogEntry::clock(lc(other_id_raw, 0, 1)).0,
                LogEntry::clock(lc(other_id_raw, 0, 1)).1,
                LogEntry::event(ev(1)),
                LogEntry::event(ev(2)),
                LogEntry::event(ev(3)),
                LogEntry::event(ev(4)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::TraceClock(lc(other_id_raw, 0, 1)),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4))
                ],
            }
        );

        mem_accessor.borrow_mut().overwrite_buffer(&vec![
            LogEntry::event(ev(5)),
            LogEntry::event(ev(6)),
            LogEntry::event(ev(7)),
            LogEntry::event(ev(8)),
            LogEntry::event(ev(9)),
            LogEntry::event(ev(10)),
            LogEntry::event(ev(11)),
            LogEntry::event(ev(12)),
        ]);
        mem_accessor.borrow_mut().set_write_seqn(16);
        mem_accessor.borrow_mut().set_overwrite_seqn(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: 1,
                frontier_clocks: vec![lc(pid_raw, 0, 1), lc(other_id_raw, 0, 1)],
                event_log: vec![
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(ev(7)),
                    EventLogEntry::Event(ev(8)),
                    EventLogEntry::Event(ev(9)),
                    EventLogEntry::Event(ev(10)),
                    EventLogEntry::Event(ev(11)),
                    EventLogEntry::Event(ev(12))
                ],
            }
        );
    }

    /// Return empty report when no logs read
    #[test]
    fn empty_read() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            0,
            0,
            &mut vec![
                LogEntry::event(ev(1)),
                LogEntry::event(ev(1)),
                LogEntry::event(ev(1)),
                LogEntry::event(ev(1)),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![],
            }
        );
    }

    /// Clock not read if only prefix has been written
    #[test]
    fn split_clock_between_reads() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            4,
            0,
            &mut vec![
                LogEntry::event(ev(1)),
                LogEntry::event(ev(2)),
                LogEntry::event(ev(3)),
                LogEntry::clock(lc(pid_raw, 0, 1)).0,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3))
                ],
            }
        );

        mem_accessor.borrow_mut().overwrite_buffer(&vec![
            LogEntry::clock(lc(pid_raw, 0, 1)).1,
            LogEntry::event(ev(4)),
            LogEntry::event(ev(5)),
            LogEntry::event(ev(6)),
        ]);
        mem_accessor.borrow_mut().set_write_seqn(8);
        mem_accessor.borrow_mut().set_overwrite_seqn(4);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: 1,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6)),
                ],
            }
        );
    }

    /// Event with payload not read if only prefix has been written
    #[test]
    fn split_payload_event_between_reads() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            4,
            0,
            &mut vec![
                LogEntry::event(ev(1)),
                LogEntry::event(ev(2)),
                LogEntry::event(ev(3)),
                LogEntry::event_with_payload(ev(4), 5).0,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn MemoryAccessor>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 0,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3))
                ],
            }
        );

        mem_accessor.borrow_mut().overwrite_buffer(&vec![
            LogEntry::event_with_payload(ev(4), 5).1,
            LogEntry::event(ev(6)),
            LogEntry::event(ev(7)),
            LogEntry::event(ev(8)),
        ]);
        mem_accessor.borrow_mut().set_write_seqn(8);
        mem_accessor.borrow_mut().set_overwrite_seqn(4);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: 1,
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithPayload(ev(4), 5),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(ev(7)),
                    EventLogEntry::Event(ev(8)),
                ],
            }
        );
    }
}
