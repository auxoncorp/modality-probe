use chrono::Utc;
use std::cell::RefCell;
use std::error::Error;
use std::fs::File;
use std::mem::size_of;
use std::net::SocketAddrV4;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::mpsc::Receiver;
use std::thread::sleep;
use std::time::Duration;
use std::convert::TryFrom;

use field_offset::offset_of;
use num::traits::Unsigned;
use probe_rs::{MemoryInterface, Session};

use modality_probe::log::LogEntry;
use modality_probe::payload::{
    write_report_payload, ClocksOverflowedError, FrontierClocks, PayloadOutput,
};
use modality_probe::{
    DynamicHistory, LogicalClock, ModalityProbe, OrdClock, OverwritePriorityLevel, ProbeEpoch,
    ProbeId, ProbeTicks,
};
use modality_probe_collector_common::{
    add_log_report_to_entries, csv::write_log_entries, Report, ReportLogEntry, SessionId,
};
use race_buffer::reader::{RaceBufferReader, Snapper};
use race_buffer::writer::RaceBuffer;
use race_buffer::PossiblyMissed;

type DynResult<T> = std::result::Result<T, Box<dyn Error>>;

// Offset of pointer to DynamicHistory in ModalityProbe struct, which is located in modality-probe/src/lib.rs
fn history_ptr_offset<W>() -> W
where
    W: Word,
{
    offset_of!(ModalityProbe => history)
        .get_byte_offset()
        .into()
}

// Address offsets of each needed field of the DynamicHistory struct, which is located in modality-probe/src/history.rs
fn overwrite_priority_offset<W>() -> W
where
    W: Word,
{
    W::try_from(offset_of!(DynamicHistory => overwrite_priority)
        .get_byte_offset()).expect("Offset cannot be greater than a word on the target system")
}

fn probe_id_offset<W>() -> W
where
    W: Word,
{
    offset_of!(DynamicHistory => probe_id)
        .get_byte_offset()
        .into()
}

fn write_seqn_offset<W>() -> W
where
    W: Word,
{
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => write_seqn)
        .get_byte_offset()
        .into()
}

fn overwrite_seqn_offset<W>() -> W
where
    W: Word,
{
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => overwrite_seqn)
        .get_byte_offset()
        .into()
}

fn log_storage_addr_offset<W>() -> W
where
    W: Word,
{
    offset_of!(DynamicHistory => log: RaceBuffer<LogEntry> => storage)
        .get_byte_offset()
        .into()
}

fn log_storage_cap_offset<W>() -> W
where
    W: Word,
{
    // Assume storage addr is a u32
    log_storage_addr_offset() + size_of::<u32>().into()
}

/// Log payload output backed by a Vector
struct PayloadOutputVec<'a>(&'a mut Vec<LogEntry>);

impl PayloadOutput for PayloadOutputVec<'_> {
    fn push(&mut self, item: LogEntry) {
        self.0.push(item)
    }

    fn free_capacity(&mut self) -> usize {
        usize::MAX
    }
}

/// Reported clocks list backed by a vector
struct FrontierClocksVec<'a>(&'a mut Vec<LogicalClock>);

impl FrontierClocks for FrontierClocksVec<'_> {
    fn merge_clock(&mut self, ext_clock: LogicalClock) -> Result<(), ClocksOverflowedError> {
        let mut existed = false;
        for c in self.0.iter_mut() {
            if c.id == ext_clock.id {
                if OrdClock(ext_clock.epoch, ext_clock.ticks) > OrdClock(c.epoch, c.ticks) {
                    c.epoch = ext_clock.epoch;
                    c.ticks = ext_clock.ticks;
                }
                existed = true;
            }
        }
        if !existed {
            self.0.push(ext_clock);
        }
        Ok(())
    }

    fn as_slice(&self) -> &[LogicalClock] {
        self.0.as_slice()
    }
}

/// Configuration for running collector
#[derive(Debug, PartialEq)]
pub struct Config<W>
where
    W: Word,
{
    pub session_id: SessionId,
    pub big_endian: bool,
    pub attach_target: Option<String>,
    pub gdb_addr: Option<SocketAddrV4>,
    pub interval: Duration,
    pub output_path: PathBuf,
    pub probe_addrs: Vec<ProbeAddr<W>>,
}

/// Struct representing a probe address, either the address of the probe itself or of
/// a pointer to the probe
#[derive(Debug, PartialEq)]
pub enum ProbeAddr<W>
where
    W: Word,
{
    Addr(W),
    PtrAddr(W),
}

pub trait Word: Unsigned + TryFrom<usize> + std::fmt::Debug {}

impl Word for u32 {}

impl Word for u64 {}

/// Trait used to specify backend used to access device memory
pub trait MemoryAccessor {
    type TargetWord: Word;

    fn read_32(&mut self, addr: Self::TargetWord) -> DynResult<u32>;
    fn read_word(&mut self, addr: Self::TargetWord) -> DynResult<Self::TargetWord>;
    fn write_32(&mut self, addr: Self::TargetWord, data: u32) -> DynResult<()>;
}

/// MemoryAccessor that uses probe-rs to access device memory
struct ProbeRsReader(Session);

impl MemoryAccessor for ProbeRsReader {
    type TargetWord = u32;
    fn read_word(&mut self, addr: Self::TargetWord) -> DynResult<Self::TargetWord> {
        self.read_32(addr)
    }
    fn read_32(&mut self, addr: u32) -> DynResult<u32> {
        let mut core = self.0.core(0)?;
        Ok(core.read_word_32(addr)?)
    }
    fn write_32(&mut self, addr: u32, data: u32) -> DynResult<()> {
        let mut core = self.0.core(0)?;
        Ok(core.write_word_32(addr, data)?)
    }
}

/// Struct used to take snapshots of RaceBuffer on device
struct MemorySnapper<W>
where
    W: Word,
{
    /// Reader used to read device memory
    mem_accessor: Rc<RefCell<dyn MemoryAccessor<TargetWord = W>>>,
    /// Address of RaceBuffer backing storage
    storage_addr: W,
    /// Address of RaceBuffer write cursor
    write_seqn_addr: W,
    /// Address of RaceBuffer overwrite cursor
    overwrite_seqn_addr: W,
}

impl<W> Snapper<LogEntry> for MemorySnapper<W>
where
    W: Word,
{
    fn snap_write_seqn(&self) -> DynResult<u32> {
        self.mem_accessor.borrow_mut().read_32(self.write_seqn_addr)
    }

    fn snap_overwrite_seqn(&self) -> DynResult<u32> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.overwrite_seqn_addr)
    }

    fn snap_storage(&self, index: u32) -> DynResult<LogEntry> {
        let raw: u32 = self
            .mem_accessor
            .borrow_mut()
            .read_32(self.storage_addr + (size_of::<LogEntry>() as u32 * index))?;
        // Safe because entry is already in memory as a valid LogEntry
        Ok(unsafe { LogEntry::new_unchecked(raw) })
    }
}

/// Used to write to probe's "overwrite_priority" field
struct PriorityWriter<W>
where
    W: Word,
{
    /// Memory accessor used to write to device memoryt
    mem_accessor: Rc<RefCell<dyn MemoryAccessor<TargetWord = W>>>,
    /// Address of priority field
    priority_field_addr: W,
}

impl<W> PriorityWriter<W>
where
    W: Word,
{
    fn write(&mut self, level: OverwritePriorityLevel) -> DynResult<()> {
        self.mem_accessor
            .borrow_mut()
            .write_32(self.priority_field_addr, level.0)
    }
}

/// Log collector for a single probe
pub struct Collector<W>
where
    W: Word,
{
    /// Sequence number of next report
    seq_num: u16,
    /// Reader used to read the probe's RaceBuffer
    reader: RaceBufferReader<LogEntry, MemorySnapper<W>>,
    /// Processed clocks backing storage
    clocks: Vec<LogicalClock>,
    /// Used to write to the probe's "overwrite_priority" field
    priority_writer: PriorityWriter<W>,
}

impl<W> Collector<W>
where
    W: Word,
{
    /// Initialize collector by reading probe information
    pub fn initialize(
        probe_addr: &ProbeAddr<W>,
        mem_accessor: Rc<RefCell<dyn MemoryAccessor<TargetWord = W>>>,
    ) -> DynResult<Self> {
        let addr = match *probe_addr {
            ProbeAddr::Addr(addr) => addr,
            // Read storage address from pointer
            ProbeAddr::PtrAddr(addr) => mem_accessor.borrow_mut().read_word(addr)?,
        };
        let mut mem_accessor_borrowed = mem_accessor.borrow_mut();
        // Get address of DynamicHistory
        let hist_addr = mem_accessor_borrowed.read_word(addr + history_ptr_offset())?;
        // Read DynamicHistory fields
        let id_raw = mem_accessor_borrowed.read_32(hist_addr + probe_id_offset())?;
        let id =
            ProbeId::new(id_raw).ok_or_else(|| "Read invalid probe ID from device".to_string())?;
        let buf_addr = mem_accessor_borrowed.read_word(hist_addr + log_storage_addr_offset())?;
        let buf_cap = mem_accessor_borrowed.read_word(hist_addr + log_storage_cap_offset())?;
        let write_seqn_addr = hist_addr + write_seqn_offset();
        let overwrite_seqn_addr = hist_addr + overwrite_seqn_offset();
        let priority_field_addr = hist_addr + overwrite_priority_offset();
        drop(mem_accessor_borrowed);

        // Initialize frontier clocks with self clock set to 0
        let mut clocks = Vec::new();
        // Clocks should not overflow in Vec; result can be unwrapped
        FrontierClocksVec(&mut clocks)
            .merge_clock(LogicalClock {
                id,
                epoch: ProbeEpoch(0),
                ticks: ProbeTicks(0),
            })
            .unwrap();

        let priority_mem_accessor = mem_accessor.clone();
        Ok(Self {
            seq_num: 0,
            reader: RaceBufferReader::new(
                MemorySnapper {
                    mem_accessor,
                    storage_addr: buf_addr,
                    write_seqn_addr,
                    overwrite_seqn_addr,
                },
                buf_cap,
            ),
            clocks,
            priority_writer: PriorityWriter {
                mem_accessor: priority_mem_accessor,
                priority_field_addr,
            },
        })
    }

    /// Collect all new logs, return a report
    pub fn collect_report(&mut self) -> DynResult<Report> {
        // Perform a RaceBuffer read
        let mut rbuf = Vec::new();
        self.retrieve_logs(&mut rbuf)?;

        let n_frontier_clocks = self.clocks.len();
        let mut processed_log = Vec::new();
        let (_n_entries_written, n_entries_read, did_clocks_overflow) = write_report_payload(
            rbuf.iter().copied(),
            &mut FrontierClocksVec(&mut self.clocks),
            &mut PayloadOutputVec(&mut processed_log),
        );
        // Should be able to process all items, clocks should not overflow
        debug_assert_eq!(n_entries_read, rbuf.len());
        debug_assert!(!did_clocks_overflow);

        match Report::try_from_log(
            self.clocks[0],
            self.seq_num,
            n_frontier_clocks,
            &processed_log[..],
        ) {
            Ok(report) => {
                self.seq_num += 1;
                Ok(report)
            }
            Err(_) => Err("Error serializing report".to_string().into()),
        }
    }

    /// Write to "write priority" field in probe
    pub fn set_overwrite_priority(&mut self, level: OverwritePriorityLevel) -> DynResult<()> {
        self.priority_writer.write(level)
    }

    /// Perform a racebuffer read
    pub(crate) fn retrieve_logs(
        &mut self,
        rbuf: &mut Vec<PossiblyMissed<LogEntry>>,
    ) -> DynResult<u32> {
        self.reader.read(rbuf)
    }
}

/// Open memory reader based on config
fn open_memory_reader<W>(
    c: &Config<W>,
) -> DynResult<Rc<RefCell<dyn MemoryAccessor<TargetWord = W>>>>
where
    W: Word,
{
    Ok(Rc::new(RefCell::new(match c.attach_target.as_ref() {
        Some(target) => {
            let session = Session::auto_attach(target)?;
            ProbeRsReader(session)
        }
        // No probe rs target implies use of gdb, which is not implemented yet
        None => unimplemented!(),
    })))
}

/// Initialize collectors of each probe based on config
fn initialize_collectors<W>(
    c: &Config<W>,
    mem_accessor: Rc<RefCell<dyn MemoryAccessor<TargetWord = W>>>,
) -> DynResult<Vec<Collector<W>>>
where
    W: Word,
{
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
) -> DynResult<()> {
    let mut entries: Vec<ReportLogEntry> = Vec::new();

    add_log_report_to_entries(&report, session_id, Utc::now(), &mut entries);
    write_log_entries(out, &entries, include_header_row)?;
    Ok(())
}

/// Run debug collector with given config
pub fn run<W>(c: &Config<W>, shutdown_receiver: Receiver<()>) -> DynResult<()>
where
    W: Word,
{
    let mem_accessor = open_memory_reader(c)?;
    let mut collectors = initialize_collectors(c, mem_accessor)?;

    let mut needs_csv_headers = !c.output_path.exists() || c.output_path.metadata()?.len() == 0;
    let mut out = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&c.output_path)?;

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

    struct DirectMemAccessor;

    impl MemoryAccessor for DirectMemAccessor {

        fn write_32(&mut self, addr: u32, data: u32) -> DynResult<()> {
            let ptr = addr as usize as *mut u32;
            unsafe { *ptr = data };
            Ok(())
        }

        fn read_32(&mut self, addr: u32) -> DynResult<u32> {
            let ptr = addr as usize as *const u32;
            Ok(unsafe { *ptr })
        }
    }

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
