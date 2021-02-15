use chrono::Utc;
use std::cell::RefCell;
use std::convert::TryFrom;
use std::fs::File;
use std::io;
use std::mem::{align_of, size_of};
use std::net::SocketAddrV4;
use std::ops::Add;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::mpsc::Receiver;
use std::thread;
use std::time::Duration;

use crossbeam_channel as channel;
use err_derive::Error;
use probe_rs::{MemoryInterface, Session};

use fenced_ring_buffer::async_reader::{FencedReader, Snapper};
use fenced_ring_buffer::WholeEntry;
use modality_probe::field_offsets::*;
use modality_probe::{
    log::LogEntry, EventId, LogicalClock, ModalityProbe, NanosecondResolution, OrdClock,
    ProbeEpoch, ProbeId, ProbeTicks, WallClockId,
};
use modality_probe_collector_common::{
    add_log_report_to_entries, json::write_log_entries, Report, ReportLogEntry, SerializationError,
    SessionId,
};

/// Either a u32 or u64, depending on the target architecture
#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash)]
pub enum Word {
    U32(u32),
    U64(u64),
}

impl Word {
    fn size(&self) -> u8 {
        match self {
            Self::U32(_) => 4,
            Self::U64(_) => 8,
        }
    }

    #[cfg(test)]
    fn unwrap_32(&self) -> u32 {
        match self {
            Self::U32(n) => *n,
            Self::U64(_) => panic!("Tried to unwrap u32 from U64 Word"),
        }
    }
}

impl Into<usize> for Word {
    fn into(self) -> usize {
        match self {
            Self::U32(n) => n as usize,
            Self::U64(n) => n as usize,
        }
    }
}

impl Into<u64> for Word {
    fn into(self) -> u64 {
        match self {
            Self::U32(n) => n as u64,
            Self::U64(n) => n,
        }
    }
}

impl Add<u64> for Word {
    type Output = Word;

    // Note: u64s added to 32 bit words must not be greater than u32::MAX
    fn add(self, rhs: u64) -> Word {
        match self {
            Word::U32(n) => Word::U32(n + u32::try_from(rhs).unwrap()),
            Word::U64(n) => Word::U64(n + rhs),
        }
    }
}

/// Configuration for running collector
#[derive(Debug, PartialEq)]
pub struct Config {
    pub session_id: SessionId,
    pub target: TargetConfig,
    pub interval: Duration,
    pub output_path: PathBuf,
    pub init_timeout: Option<Duration>,
    pub probe_addrs: Vec<ProbeAddr>,
}

/// Target device, either directly through probe-rs or by proxy through a gdb server
#[derive(Debug, PartialEq)]
pub enum TargetConfig {
    ProbeRsTarget(String),
    GdbAddr(SocketAddrV4),
}

/// Struct representing a probe address, either the address of the probe itself or of
/// a pointer to the probe
#[derive(Debug, PartialEq)]
pub enum ProbeAddr {
    Addr(Word),
    PtrAddr(Word),
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(display = "Error interacting with target: {}", _0)]
    TargetError(#[error(from)] TargetError),
    #[error(display = "There is no probe at address {:X}", _0)]
    NoProbeAtAddress(u64),
    #[error(
        display = "Pointer at address {:X} does not point to a valid probe",
        _0
    )]
    InvalidProbePointer(u64),
    #[error(display = "Invalid probe id read from target probe")]
    InvalidProbeId,
    #[error(display = "Invalid probe id read from log")]
    InvalidClockProbeId,
    #[error(display = "Error serializing the report: {}", _0)]
    ReportSerializationError(SerializationError),
    #[error(display = "Error writing entries to file: {}", _0)]
    OutputWritingError(modality_probe_collector_common::Error),
    #[error(display = "Error opening output file: {}", _0)]
    FileError(#[error(from)] io::Error),
}

#[derive(Debug, Error)]
pub enum TargetError {
    #[error(display = "No probes found to attach to; check connection to chip")]
    NoProbesConnected,
    #[error(display = "{}", _0)]
    ProbeRsError(probe_rs::Error),
    #[error(display = "Cannot directly attach to 64 bit chips")]
    MustBe32Bit,
}

/// Trait used to specify backend used to access device memory
pub trait Target {
    fn reset(&mut self) -> Result<(), TargetError>;
    fn read_word(&mut self, addr: Word) -> Result<Word, TargetError>;
    fn read_32(&mut self, addr: Word) -> Result<u32, TargetError>;
    fn read_byte(&mut self, addr: Word) -> Result<u8, TargetError>;
    fn write_32(&mut self, addr: Word, data: u32) -> Result<(), TargetError>;
}

/// Target that uses probe-rs to access device memory
struct ProbeRsTarget(Session);

impl Target for ProbeRsTarget {
    fn reset(&mut self) -> Result<(), TargetError> {
        let mut core = self.0.core(0).map_err(TargetError::ProbeRsError)?;
        core.reset().map_err(TargetError::ProbeRsError)
    }

    fn read_word(&mut self, addr: Word) -> Result<Word, TargetError> {
        self.read_32(addr).map(Word::U32)
    }

    fn read_32(&mut self, addr: Word) -> Result<u32, TargetError> {
        if let Word::U32(addr_raw) = addr {
            let mut core = self.0.core(0).map_err(TargetError::ProbeRsError)?;
            core.read_word_32(addr_raw)
                .map_err(TargetError::ProbeRsError)
        } else {
            // ProbeRs does not support 64 bit targets
            Err(TargetError::MustBe32Bit)
        }
    }

    fn read_byte(&mut self, addr: Word) -> Result<u8, TargetError> {
        if let Word::U32(addr_raw) = addr {
            let mut core = self.0.core(0).map_err(TargetError::ProbeRsError)?;
            let mut res = [0u8];
            core.read_8(addr_raw, &mut res)
                .map_err(TargetError::ProbeRsError)?;
            Ok(res[0])
        } else {
            // ProbeRs does not support 64 bit targets
            Err(TargetError::MustBe32Bit)
        }
    }

    fn write_32(&mut self, addr: Word, data: u32) -> Result<(), TargetError> {
        if let Word::U32(addr_raw) = addr {
            let mut core = self.0.core(0).map_err(TargetError::ProbeRsError)?;
            core.write_word_32(addr_raw, data)
                .map_err(TargetError::ProbeRsError)
        } else {
            // ProbeRs does not support 64 bit targets
            Err(TargetError::MustBe32Bit)
        }
    }
}

/// Struct used to take snapshots of FencedRingBuffer on device
struct MemorySnapper {
    /// Reader used to read device memory
    mem_accessor: Rc<RefCell<dyn Target>>,
    /// Address of FencedRingBuffer backing storage
    storage_addr: Word,
    /// Address of FencedRingBuffer write sequence number high word
    write_seqn_high_addr: Word,
    /// Address of FencedRingBuffer write sequence number low word
    write_seqn_low_addr: Word,
    /// Address of FencedRingBuffer write sequence number high word
    overwrite_seqn_high_addr: Word,
    /// Address of FencedRingBuffer write sequence number low word
    overwrite_seqn_low_addr: Word,
}

impl Snapper<LogEntry> for MemorySnapper {
    type Error = TargetError;

    fn snap_write_seqn_high(&self) -> Result<u32, TargetError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.write_seqn_high_addr)
    }

    fn snap_write_seqn_low(&self) -> Result<u32, TargetError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.write_seqn_low_addr)
    }

    fn snap_overwrite_seqn_high(&self) -> Result<u32, TargetError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.overwrite_seqn_high_addr)
    }

    fn snap_overwrite_seqn_low(&self) -> Result<u32, TargetError> {
        self.mem_accessor
            .borrow_mut()
            .read_32(self.overwrite_seqn_low_addr)
    }

    fn snap_storage(&self, index: usize) -> Result<LogEntry, TargetError> {
        let raw: u32 = self
            .mem_accessor
            .borrow_mut()
            .read_32(self.storage_addr + (size_of::<LogEntry>() * index) as u64)?;
        // Safe because entry is already in memory as a valid LogEntry
        Ok(unsafe { LogEntry::new_unchecked(raw) })
    }
}

/// Used to write to probe's "overwrite_priority" field
struct PriorityWriter {
    /// Memory accessor used to write to device memory
    mem_accessor: Rc<RefCell<dyn Target>>,
    /// Address of priority field
    priority_field_addr: Word,
}

impl PriorityWriter {
    fn write(&mut self, level: u32) -> Result<(), TargetError> {
        self.mem_accessor
            .borrow_mut()
            .write_32(self.priority_field_addr, level)
    }
}

/// Log collector for a single probe
pub struct Collector {
    /// Sequence number of next report
    seq_num: u64,
    /// Reader used to read the probe's FencedRingBuffer
    reader: FencedReader<LogEntry, MemorySnapper>,
    /// Temporary storage for trailing paired wall clock time entry
    prev_paired_wall_clock_time: Option<WholeEntry<LogEntry>>,
    /// Allocated buffer for reading the log into
    rbuf: Vec<WholeEntry<LogEntry>>,
    /// Processed clocks backing storage
    clocks: Vec<LogicalClock>,
    /// Used to write to the probe's "overwrite_priority" field
    priority_writer: PriorityWriter,
    /// Time resolution extracted from the probe
    time_resolution: NanosecondResolution,
    /// Wall clock id extracted from the probe
    wall_clock_id: WallClockId,
    /// Persistent epoch counting flag extracted from the probe
    persistent_epoch_counting: bool,
}

impl Collector {
    /// Initialize collector by reading probe information
    pub fn initialize(
        probe_addr: &ProbeAddr,
        mem_accessor: Rc<RefCell<dyn Target>>,
    ) -> Result<Self, Error> {
        let addr = Self::find_probe(probe_addr, mem_accessor.clone())?;
        let (hist_addr, id, time_res, wall_clock_id, persistent_epoch_counting, buf_addr, buf_cap) = {
            let mut mem = mem_accessor.borrow_mut();
            // Get address of DynamicHistory
            let hist_addr = mem.read_word(addr + history_ptr_offset())?;
            // Read DynamicHistory fields
            let id_raw = mem.read_32(hist_addr + probe_id_offset())?;
            let id = ProbeId::new(id_raw).ok_or(Error::InvalidProbeId)?;
            let time_res = mem.read_32(hist_addr + time_resolution_offset())?;
            // NOTE: probe-rs does have read_16
            let wall_clock_id = mem.read_32(hist_addr + wall_clock_id_offset())? as u16;
            let persistent_epoch_counting =
                mem.read_byte(hist_addr + persistent_epoch_counting_offset())?;
            let buf_addr = mem.read_word(hist_addr + log_storage_addr_offset())?;
            let buf_cap = mem
                .read_word(hist_addr + log_storage_cap_offset(hist_addr.size()))?
                .into();
            (
                hist_addr,
                id,
                time_res,
                wall_clock_id,
                persistent_epoch_counting,
                buf_addr,
                buf_cap,
            )
        };
        let write_seqn_high_addr = hist_addr + write_seqn_high_offset();
        let write_seqn_low_addr = hist_addr + write_seqn_low_offset();
        let overwrite_seqn_high_addr = hist_addr + overwrite_seqn_high_offset();
        let overwrite_seqn_low_addr = hist_addr + overwrite_seqn_low_offset();
        let priority_field_addr = hist_addr + overwrite_priority_offset();

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
            reader: FencedReader::new(
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
            prev_paired_wall_clock_time: None,
            rbuf: Vec::new(),
            clocks,
            priority_writer: PriorityWriter {
                mem_accessor: priority_mem_accessor,
                priority_field_addr,
            },
            time_resolution: time_res.into(),
            wall_clock_id: wall_clock_id.into(),
            persistent_epoch_counting: persistent_epoch_counting != 0,
        })
    }

    fn find_probe(
        probe_addr: &ProbeAddr,
        mem_accessor: Rc<RefCell<dyn Target>>,
    ) -> Result<Word, Error> {
        match *probe_addr {
            ProbeAddr::Addr(addr) => {
                let padded_probe_address = Self::scan_guard_bytes(addr, mem_accessor.clone())?
                    .ok_or_else(|| Error::NoProbeAtAddress(addr.into()))?;
                // Ensure probe has correct fingerprint
                let fingerprint = mem_accessor.borrow_mut().read_32(padded_probe_address)?;
                if fingerprint != ModalityProbe::STRUCT_FINGERPRINT {
                    Err(Error::NoProbeAtAddress(addr.into()))
                } else {
                    Ok(padded_probe_address)
                }
            }
            // Read address from pointer
            ProbeAddr::PtrAddr(ptr_addr) => {
                let deref_addr = mem_accessor.borrow_mut().read_word(ptr_addr)?;
                let padded_probe_address =
                    Self::scan_guard_bytes(deref_addr, mem_accessor.clone())?
                        .ok_or_else(|| Error::InvalidProbePointer(ptr_addr.into()))?;

                // Ensure probe has correct fingerprint
                let fingerprint = mem_accessor.borrow_mut().read_32(padded_probe_address)?;
                if fingerprint != ModalityProbe::STRUCT_FINGERPRINT {
                    Err(Error::InvalidProbePointer(ptr_addr.into()))
                } else {
                    Ok(padded_probe_address)
                }
            }
        }
    }

    /// Loops through probe guard bytes starting at addr, returning the address of the first byte
    /// after the guard bytes, or None if the guard bytes repeat for more than twice the alignment of a probe
    fn scan_guard_bytes(
        addr: Word,
        mem_accessor: Rc<RefCell<dyn Target>>,
    ) -> Result<Option<Word>, Error> {
        let mut mem = mem_accessor.borrow_mut();
        // Max guard bytes we are willing to check. In reality, the probe should appear within only 1 alignment
        const MAX_GUARD_BYTES: usize = align_of::<ModalityProbe>() * 2;

        for i in 0..MAX_GUARD_BYTES {
            let cur_addr = addr + (i as u64);
            let b = mem.read_byte(cur_addr)?;
            if b == ModalityProbe::PADDING_GUARD_BYTE {
                continue;
            } else {
                return Ok(Some(cur_addr));
            }
        }
        Ok(None)
    }

    /// Collect all new logs, return a report
    pub fn collect_report(&mut self) -> Result<Option<Report>, Error> {
        self.rbuf.clear();

        let num_missed = self.reader.read(&mut self.rbuf)?;

        // Possibly add entries missed event
        if num_missed > 0 {
            let num_missed_rounded = u64::min(num_missed, u32::MAX as u64) as u32;
            let (ev, payload) =
                LogEntry::event_with_payload(EventId::EVENT_LOG_ITEMS_MISSED, num_missed_rounded);
            self.rbuf.insert(0, WholeEntry::Double(ev, payload));

            if let Some(e) = self.prev_paired_wall_clock_time.take() {
                eprintln!("Warning: dropping paired wall clock time entry {:?} from previous report because items were missed and the associated entry was lost", e);
            }
        } else if let Some(e) = self.prev_paired_wall_clock_time.take() {
            // Insert paired wall clock time entry from previous report if needed
            self.rbuf.insert(0, e);
        }

        if self.rbuf.is_empty() {
            // No entries to report
            return Ok(None);
        }

        // If the last entry is a paired wall clock time entry, then
        // save it for the next report so its not fragmented away from
        // its associated entry
        if let Some(e) = self.rbuf.last() {
            if e.is_double() && e.first_entry().has_wall_clock_time_paired_bit_set() {
                self.prev_paired_wall_clock_time =
                    Some(self.rbuf.pop().expect("Just checked last entry"));
            }
        }

        // Add report produced event
        self.rbuf.push(WholeEntry::Single(LogEntry::event(
            EventId::EVENT_PRODUCED_EXTERNAL_REPORT,
        )));

        // Keep a copy of the clocks before this report which will be used as frontier clocks
        let report_clocks = self.clocks.clone();

        // Merge clocks from this report
        for entry in self.rbuf.iter() {
            if let WholeEntry::Double(first, second) = entry {
                if first.has_clock_bit_set() {
                    let id = ProbeId::new(first.interpret_as_logical_clock_probe_id())
                        .ok_or(Error::InvalidClockProbeId)?;
                    let (epoch, ticks) = modality_probe::unpack_clock_word(second.raw());
                    Self::merge_clock(&mut self.clocks, LogicalClock { id, epoch, ticks })
                }
            }
        }

        Report::try_from_log(self.clocks[0], self.seq_num, report_clocks, &self.rbuf[..])
            .map(|mut report| {
                self.seq_num += 1;
                report.time_resolution = self.time_resolution;
                report.wall_clock_id = self.wall_clock_id;
                report.persistent_epoch_counting = self.persistent_epoch_counting;
                report
            })
            .map(Some)
            .map_err(Error::ReportSerializationError)
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
                break;
            }
        }
        if !existed {
            clocks.push(ext_clock);
        }
    }

    /// Write to "write priority" field in probe
    pub fn set_overwrite_priority(&mut self, level: u32) -> Result<(), TargetError> {
        self.priority_writer.write(level)
    }
}

/// Open memory accessor based on config
fn open_mem_accessor(c: &Config) -> Result<Rc<RefCell<dyn Target>>, TargetError> {
    match &c.target {
        TargetConfig::ProbeRsTarget(target) => {
            let probes = probe_rs::Probe::list_all();
            if probes.is_empty() {
                return Err(TargetError::NoProbesConnected);
            }
            let probe = probes[0]
                .open()
                .map_err(|e| TargetError::ProbeRsError(e.into()))?;
            let session = probe.attach(target).map_err(TargetError::ProbeRsError)?;
            Ok(Rc::new(RefCell::new(ProbeRsTarget(session))))
        }
        // No probe rs target implies use of gdb, which is not implemented yet
        TargetConfig::GdbAddr(_) => unimplemented!(),
    }
}

/// Initialize collectors of each probe based on config
fn initialize_collectors(
    c: &Config,
    mem_accessor: Rc<RefCell<dyn Target>>,
) -> Result<Vec<Collector>, Error> {
    let mut collectors = Vec::new();
    for probe_addr in c.probe_addrs.iter() {
        collectors.push(Collector::initialize(probe_addr, mem_accessor.clone())?);
    }
    Ok(collectors)
}

/// Write report to given file
fn report_to_file(out: &mut File, report: Report, session_id: SessionId) -> Result<(), Error> {
    let mut entries: Vec<ReportLogEntry> = Vec::new();

    add_log_report_to_entries(&report, session_id, Utc::now(), &mut entries)
        .map_err(Error::OutputWritingError)?;
    write_log_entries(out, &entries).map_err(Error::OutputWritingError)
}

/// Run debug collector with given config
pub fn run(c: &Config, shutdown_receiver: Receiver<()>) -> Result<(), Error> {
    // Translate std shutdown channel to crossbeam channel
    let (shutdown_sender_crossbeam, shutdown_receiver_crossbeam) = channel::unbounded();
    thread::spawn(move || {
        shutdown_receiver.recv().unwrap();
        shutdown_sender_crossbeam.send(()).unwrap();
    });

    let mem_accessor = open_mem_accessor(c)?;
    if let Some(timeout) = c.init_timeout {
        mem_accessor.borrow_mut().reset()?;
        channel::select! {
            recv(shutdown_receiver_crossbeam) -> _ => return Ok(()),
            default(timeout) => (),
        }
    }
    let mut collectors = initialize_collectors(c, mem_accessor)?;
    let mut out = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&c.output_path)?;
    loop {
        for collector in &mut collectors {
            if let Some(report) = collector.collect_report()? {
                report_to_file(&mut out, report, c.session_id)?;
            }
        }

        channel::select! {
            recv(shutdown_receiver_crossbeam) -> _ => return Ok(()),
            default(c.interval) => (),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use maplit::hashmap;
    use pretty_assertions::assert_eq;
    use std::collections::HashMap;
    use std::convert::TryInto;
    use std::ptr;

    use modality_probe::{
        time::{NanosecondResolution, Nanoseconds, WallClockId},
        EventId, ModalityProbe, Probe, RestartCounterProvider,
    };
    use modality_probe_collector_common::{EventLogEntry, SequenceNumber};
    use std::mem::MaybeUninit;

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

    struct DirectMemAccessor;

    impl Target for DirectMemAccessor {
        fn reset(&mut self) -> Result<(), TargetError> {
            // Cannot reset own execution
            unimplemented!()
        }

        fn write_32(&mut self, addr: Word, data: u32) -> Result<(), TargetError> {
            let ptr = match addr {
                Word::U32(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u32>());
                    addr_raw as usize as *mut u32
                }
                Word::U64(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u64>());
                    addr_raw as usize as *mut u32
                }
            };
            unsafe { *ptr = data };
            Ok(())
        }

        fn read_32(&mut self, addr: Word) -> Result<u32, TargetError> {
            let ptr = match addr {
                Word::U32(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u32>());
                    addr_raw as usize as *const u32
                }
                Word::U64(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u64>());
                    addr_raw as usize as *const u32
                }
            };
            Ok(unsafe { *ptr })
        }

        fn read_byte(&mut self, addr: Word) -> Result<u8, TargetError> {
            let ptr = match addr {
                Word::U32(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u32>());
                    addr_raw as usize as *const u8
                }
                Word::U64(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u64>());
                    addr_raw as usize as *const u8
                }
            };
            Ok(unsafe { *ptr })
        }

        fn read_word(&mut self, addr: Word) -> Result<Word, TargetError> {
            match addr {
                Word::U32(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u32>());
                    let ptr = addr_raw as usize as *const u32;
                    Ok(unsafe { Word::U32(*ptr) })
                }
                Word::U64(addr_raw) => {
                    assert!(size_of::<usize>() == size_of::<u64>());
                    let ptr = addr_raw as usize as *const u64;
                    Ok(unsafe { Word::U64(*ptr) })
                }
            }
        }
    }

    #[test]
    fn local_probe() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mut probe = ModalityProbe::new_with_storage(
            &mut storage[..],
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw = &probe as *const ModalityProbe as usize;
        #[cfg(target_pointer_width = "32")]
        let addr = Word::U32(addr_raw as u32);
        #[cfg(target_pointer_width = "64")]
        let addr = Word::U64(addr_raw as u64);

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        )
        .unwrap();

        probe.record_event(ev(1));
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(probe_id.get_raw(), 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        )
    }

    #[test]
    fn local_misaligned() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let offset = 1 + storage.as_ptr().align_offset(align_of::<ModalityProbe>());
        let storage_unaligned = &mut storage[offset..];
        let storage_unaligned_ptr = storage_unaligned.as_ptr();

        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let probe = ModalityProbe::initialize_at(
            storage_unaligned,
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let padding_len = (align_of::<ModalityProbe>() - 1) as isize;
        for i in 0..padding_len {
            assert_eq!(
                unsafe { (*(storage_unaligned_ptr.offset(i as isize))).assume_init() },
                ModalityProbe::PADDING_GUARD_BYTE
            );
        }
        assert_eq!(
            unsafe { *(storage_unaligned_ptr.offset(padding_len) as *const u32) },
            ModalityProbe::STRUCT_FINGERPRINT
        );

        let addr_raw = storage_unaligned_ptr as usize;
        #[cfg(target_pointer_width = "32")]
        let addr = Word::U32(addr_raw as u32);
        #[cfg(target_pointer_width = "64")]
        let addr = Word::U64(addr_raw as u64);

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        )
        .unwrap();

        probe.record_event(ev(1));
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(probe_id.get_raw(), 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        )
    }

    #[test]
    fn local_invalid_address() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let probe = ModalityProbe::new_with_storage(
            &mut storage[..],
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw = &probe as *const ModalityProbe as usize + 512;
        #[cfg(target_pointer_width = "32")]
        let addr = Word::U32(addr_raw as u32);
        #[cfg(target_pointer_width = "64")]
        let addr = Word::U64(addr_raw as u64);

        let res = Collector::initialize(
            &ProbeAddr::Addr(addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        );
        match res {
            Ok(_) => panic!("Collector should not have initialized with an invalid probe address"),
            Err(err) => match err {
                Error::NoProbeAtAddress(err_addr) => assert_eq!(err_addr, addr_raw as u64),
                _ => panic!("Wrong error"),
            },
        }
    }

    #[test]
    fn local_invalid_ptr() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let probe = ModalityProbe::new_with_storage(
            &mut storage[..],
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw = &probe as *const ModalityProbe as usize + 512;
        let ptr_addr_raw = &addr_raw as *const usize as usize;
        #[cfg(target_pointer_width = "32")]
        let ptr_addr = Word::U32(ptr_addr_raw as u32);
        #[cfg(target_pointer_width = "64")]
        let ptr_addr = Word::U64(ptr_addr_raw as u64);

        let res = Collector::initialize(
            &ProbeAddr::PtrAddr(ptr_addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        );
        match res {
            Ok(_) => panic!("Collector should not have initialized with an invalid probe pointer"),
            Err(err) => match err {
                Error::InvalidProbePointer(err_addr) => assert_eq!(err_addr, ptr_addr_raw as u64),
                _ => panic!("Wrong error"),
            },
        }
    }

    #[test]
    fn local_probe_interaction() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let mut probe = ModalityProbe::new_with_storage(
            &mut storage[..],
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw = &probe as *const ModalityProbe as usize;

        let mut storage_2 = [MaybeUninit::new(0u8); 1024];
        let pid_raw_2 = 2;
        let probe_id_2 = ProbeId::new(pid_raw_2).unwrap();
        let mut probe_2 = ModalityProbe::new_with_storage(
            &mut storage_2[..],
            probe_id_2,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw_2 = &probe_2 as *const ModalityProbe as usize;

        #[cfg(target_pointer_width = "32")]
        let (addr, addr_2) = (Word::U32(addr_raw as u32), Word::U32(addr_raw_2 as u32));
        #[cfg(target_pointer_width = "64")]
        let (addr, addr_2) = (Word::U64(addr_raw as u64), Word::U64(addr_raw_2 as u64));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        )
        .unwrap();

        let mut collector_2 = Collector::initialize(
            &ProbeAddr::Addr(addr_2),
            Rc::new(RefCell::new(DirectMemAccessor)),
        )
        .unwrap();

        probe.record_event(ev(1));
        probe_2.record_event(ev(1));
        let snap = probe.produce_snapshot();
        probe_2.merge_snapshot(&snap);

        let report = collector_2.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id: probe_id_2,
                probe_clock: lc(pid_raw_2, 0, 1),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw_2, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw_2, 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::TraceClock(lc(pid_raw_2, 0, 1)),
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );

        probe_2.record_event(ev(2));
        let second_snap = probe_2.produce_snapshot();
        probe.merge_snapshot(&second_snap);

        let second_report = collector_2.collect_report().unwrap().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id: probe_id_2,
                probe_clock: lc(pid_raw_2, 0, 2),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw_2, 0, 1), lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::TraceClock(lc(pid_raw_2, 0, 2)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );

        let third_report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            third_report,
            Report {
                probe_id: probe_id,
                probe_clock: lc(pid_raw, 0, 2),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 2)),
                    EventLogEntry::TraceClock(lc(pid_raw_2, 0, 1)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );

        probe.record_event(ev(2));

        let fourth_report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            fourth_report,
            Report {
                probe_id: probe_id,
                probe_clock: lc(pid_raw, 0, 2),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 2), lc(pid_raw_2, 0, 1)],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
                event_log: vec![
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
            }
        );
    }

    #[test]
    fn local_probe_writeback() {
        let mut storage = [MaybeUninit::new(0u8); 1024];
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let probe = ModalityProbe::new_with_storage(
            &mut storage[..],
            probe_id,
            NanosecondResolution::UNSPECIFIED,
            WallClockId::local_only(),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();
        let addr_raw = &probe as *const ModalityProbe as usize;
        #[cfg(target_pointer_width = "32")]
        let addr = Word::U32(addr_raw as u32);
        #[cfg(target_pointer_width = "64")]
        let addr = Word::U64(addr_raw as u64);

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(addr),
            Rc::new(RefCell::new(DirectMemAccessor)),
        )
        .unwrap();

        collector.set_overwrite_priority(1).unwrap();
        assert_eq!(probe.get_overwrite_priority_level(), 1);
    }

    struct HashMapMemAccessor(HashMap<Word, u32>);

    impl HashMapMemAccessor {
        const PROBE_PTR_ADDR: Word = Word::U32(0x0);
        const PROBE_ADDR: Word = Word::U32(0x8);
        const HIST_ADDR: Word = Word::U32(0x16);
        const STORAGE_ADDR: Word = Word::U32(0x200);

        fn new(
            probe_id: ProbeId,
            write_seqn: u32,
            overwrite_seqn: u32,
            buf_contents: &Vec<LogEntry>,
        ) -> Self {
            let map = hashmap! {
                Self::PROBE_PTR_ADDR => Self::PROBE_ADDR.unwrap_32(),
                Self::PROBE_ADDR => ModalityProbe::STRUCT_FINGERPRINT,
                Self::PROBE_ADDR + history_ptr_offset() => Self::HIST_ADDR.unwrap_32(),
                Self::HIST_ADDR + probe_id_offset() => probe_id.get().into(),
                Self::HIST_ADDR + time_resolution_offset() => NanosecondResolution::UNSPECIFIED.into(),
                Self::HIST_ADDR + wall_clock_id_offset() => WallClockId::LOCAL_ONLY.0 as u32,
                Self::HIST_ADDR + persistent_epoch_counting_offset() => 0,
                Self::HIST_ADDR + log_storage_addr_offset() => Self::STORAGE_ADDR.unwrap_32(),
                Self::HIST_ADDR + log_storage_cap_offset(Word::U32(0).size()) => buf_contents.len() as u32,
                Self::HIST_ADDR + write_seqn_high_offset() => 0,
                Self::HIST_ADDR + write_seqn_low_offset() => write_seqn,
                Self::HIST_ADDR + overwrite_seqn_high_offset() => 0,
                Self::HIST_ADDR + overwrite_seqn_low_offset() => overwrite_seqn,
            };
            let mut reader = HashMapMemAccessor(map);
            reader.overwrite_buffer(&buf_contents);
            reader
        }

        fn overwrite_buffer(&mut self, buf_contents: &Vec<LogEntry>) {
            for (index, entry) in buf_contents.iter().enumerate() {
                self.0
                    .insert(Self::STORAGE_ADDR + 4 * index as u64, entry.raw());
            }
        }

        fn set_write_seqn(&mut self, new_write_seqn: u32) {
            self.0
                .insert(Self::HIST_ADDR + write_seqn_low_offset(), new_write_seqn);
        }

        fn set_overwrite_seqn(&mut self, new_overwrite_seqn: u32) {
            self.0.insert(
                Self::HIST_ADDR + overwrite_seqn_low_offset(),
                new_overwrite_seqn,
            );
        }
    }

    impl Target for HashMapMemAccessor {
        fn reset(&mut self) -> Result<(), TargetError> {
            unimplemented!()
        }

        fn read_word(&mut self, addr: Word) -> Result<Word, TargetError> {
            self.read_32(addr).map(|res| Word::U32(res))
        }

        fn read_32(&mut self, addr: Word) -> Result<u32, TargetError> {
            Ok(*self.0.get(&addr).unwrap())
        }

        fn read_byte(&mut self, addr: Word) -> Result<u8, TargetError> {
            let res = *self.0.get(&addr).unwrap();
            Ok(res.to_le_bytes()[0])
        }

        fn write_32(&mut self, _: Word, _: u32) -> Result<(), TargetError> {
            unimplemented!()
        }
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();

        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();

        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithPayload(EventId::EVENT_LOG_ITEMS_MISSED, 2),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::TraceClock(lc(other_id_raw, 0, 1)),
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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

        let second_report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 1), lc(other_id_raw, 0, 1)],
                event_log: vec![
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(ev(7)),
                    EventLogEntry::Event(ev(8)),
                    EventLogEntry::Event(ev(9)),
                    EventLogEntry::Event(ev(10)),
                    EventLogEntry::Event(ev(11)),
                    EventLogEntry::Event(ev(12)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert!(report.is_none());
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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

        let second_report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 1),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(pid_raw, 0, 1)),
                    EventLogEntry::Event(ev(4)),
                    EventLogEntry::Event(ev(5)),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(1)),
                    EventLogEntry::Event(ev(2)),
                    EventLogEntry::Event(ev(3)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
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

        let second_report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            second_report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithPayload(ev(4), 5),
                    EventLogEntry::Event(ev(6)),
                    EventLogEntry::Event(ev(7)),
                    EventLogEntry::Event(ev(8)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );
    }

    #[test]
    fn fragmented_paired_wall_clock_time_entries_are_carried_over() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let (a, b) = LogEntry::paired_wall_clock_time(Nanoseconds::new(1).unwrap());
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            3,
            0,
            &mut vec![LogEntry::event(ev(10)), a, b],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(10)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );

        mem_accessor
            .borrow_mut()
            .overwrite_buffer(&vec![LogEntry::event(ev(11)), LogEntry::event(ev(12))]);
        mem_accessor.borrow_mut().set_write_seqn(5);
        mem_accessor.borrow_mut().set_overwrite_seqn(2);

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithTime(Nanoseconds::new(1).unwrap(), ev(11)),
                    EventLogEntry::Event(ev(12)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );
    }

    #[test]
    fn fragmented_paired_wall_clock_time_entries_are_dropped_when_items_are_missed() {
        let pid_raw = 1;
        let probe_id = ProbeId::new(pid_raw).unwrap();
        let (a, b) = LogEntry::paired_wall_clock_time(Nanoseconds::new(1).unwrap());
        let mem_accessor = Rc::new(RefCell::new(HashMapMemAccessor::new(
            probe_id,
            3,
            0,
            &mut vec![LogEntry::event(ev(10)), a, b],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemAccessor::PROBE_ADDR),
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(ev(10)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );

        mem_accessor
            .borrow_mut()
            .overwrite_buffer(&vec![LogEntry::event(ev(11)), LogEntry::event(ev(12))]);
        mem_accessor.borrow_mut().set_write_seqn(5);
        mem_accessor.borrow_mut().set_overwrite_seqn(4);

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(pid_raw, 0, 0),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(pid_raw, 0, 0)],
                event_log: vec![
                    EventLogEntry::EventWithPayload(EventId::EVENT_LOG_ITEMS_MISSED, 1),
                    EventLogEntry::Event(ev(12)),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution::UNSPECIFIED,
                wall_clock_id: WallClockId::default(),
            }
        );
    }

    struct ProbeInMemAccessor {
        // Address of the storage buffer given to ModalityProbe::initialize_at()
        storage_addr: u64,
    }

    impl Target for ProbeInMemAccessor {
        fn reset(&mut self) -> Result<(), TargetError> {
            unimplemented!()
        }

        fn read_word(&mut self, addr: Word) -> Result<Word, TargetError> {
            match addr {
                Word::U64(addr) => {
                    assert!(addr >= self.storage_addr);
                    let src = addr as *const u64;
                    Ok(Word::U64(unsafe { ptr::read_volatile(src) }))
                }
                _ => unimplemented!(),
            }
        }

        fn read_32(&mut self, addr: Word) -> Result<u32, TargetError> {
            match addr {
                Word::U64(addr) => {
                    assert!(addr >= self.storage_addr);
                    let src = addr as *const u32;
                    Ok(unsafe { ptr::read_volatile(src) })
                }
                _ => unimplemented!(),
            }
        }

        fn read_byte(&mut self, addr: Word) -> Result<u8, TargetError> {
            match addr {
                Word::U64(addr) => {
                    assert!(addr >= self.storage_addr);
                    let src = addr as *const u8;
                    Ok(unsafe { ptr::read_volatile(src) })
                }
                _ => unimplemented!(),
            }
        }

        fn write_32(&mut self, _: Word, _: u32) -> Result<(), TargetError> {
            unimplemented!()
        }
    }

    #[test]
    fn on_device_probe_missed_entries_are_detectable() {
        const STORAGE_CAP: usize = 512;
        const LOG_CAP: usize = 78;
        let mut storage = [MaybeUninit::new(0u8); STORAGE_CAP];
        let storage_addr = storage.as_ptr() as *const _ as u64;

        let probe_id = ProbeId::new(1).unwrap();
        let probe = ModalityProbe::initialize_at(
            &mut storage,
            probe_id,
            NanosecondResolution(123),
            WallClockId(1),
            RestartCounterProvider::NoRestartTracking,
        )
        .unwrap();

        let mem_accessor = Rc::new(RefCell::new(ProbeInMemAccessor { storage_addr }));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(Word::U64(storage_addr)),
            mem_accessor.clone() as Rc<RefCell<dyn Target>>,
        )
        .unwrap();

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(probe_id.get_raw(), 0, 0),
                seq_num: SequenceNumber(0),
                frontier_clocks: vec![lc(probe_id.get_raw(), 0, 0)],
                event_log: vec![
                    EventLogEntry::TraceClock(lc(probe_id.get_raw(), 0, 0)),
                    EventLogEntry::Event(EventId::EVENT_PROBE_INITIALIZED),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution(123),
                wall_clock_id: WallClockId(1),
            }
        );

        let event_a = EventId::new(8888).unwrap();
        probe.record_event(event_a);

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(probe_id.get_raw(), 0, 0),
                seq_num: SequenceNumber(1),
                frontier_clocks: vec![lc(probe_id.get_raw(), 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(event_a),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution(123),
                wall_clock_id: WallClockId(1),
            }
        );

        // Fill up the log, overwriting 2 entries
        let event_b = EventId::new(9999).unwrap();
        let num_events = LOG_CAP + 2;
        let mut expected_event_log = Vec::new();
        for _ in 0..num_events {
            probe.record_event(event_b);
            expected_event_log.push(EventLogEntry::Event(event_b));
        }

        // Shave off the expected overwritten entries
        while expected_event_log.len() > LOG_CAP {
            let _ = expected_event_log.remove(0);
        }

        // Debug collector puts these events in
        expected_event_log.insert(
            0,
            EventLogEntry::EventWithPayload(EventId::EVENT_LOG_ITEMS_MISSED, 2),
        );
        expected_event_log.push(EventLogEntry::Event(
            EventId::EVENT_PRODUCED_EXTERNAL_REPORT,
        ));

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(report.event_log.len(), LOG_CAP + 2);
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(probe_id.get_raw(), 0, 0),
                seq_num: SequenceNumber(2),
                frontier_clocks: vec![lc(probe_id.get_raw(), 0, 0)],
                event_log: expected_event_log,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution(123),
                wall_clock_id: WallClockId(1),
            }
        );

        // All caught up, shouldn't miss any events this go around
        let event_a = EventId::new(8888).unwrap();
        probe.record_event(event_a);
        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(probe_id.get_raw(), 0, 0),
                seq_num: SequenceNumber(3),
                frontier_clocks: vec![lc(probe_id.get_raw(), 0, 0)],
                event_log: vec![
                    EventLogEntry::Event(event_a),
                    EventLogEntry::Event(EventId::EVENT_PRODUCED_EXTERNAL_REPORT)
                ],
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution(123),
                wall_clock_id: WallClockId(1),
            }
        );

        // Do another round of overwriting, with time, should end with with 2 missed items
        let event_c = EventId::new(7777).unwrap();
        let num_events = 1 + (LOG_CAP / 4);
        let mut expected_event_log = Vec::new();
        for i in 0..num_events {
            let payload = 0xFF00_0000 + (i as u32);
            let time = Nanoseconds::new(i as u64).unwrap();
            probe.record_event_with_payload_with_time(event_c, payload, time);

            // NOTE: debug-collector bug, see issue #288
            // Wall clock time portion will be dropped
            if i == 0 {
                expected_event_log.push(EventLogEntry::EventWithPayload(event_c, payload));
            } else {
                expected_event_log.push(EventLogEntry::EventWithPayloadWithTime(
                    time, event_c, payload,
                ));
            }
        }

        // Shave off the expected overwritten entries
        while expected_event_log.len() > LOG_CAP {
            let _ = expected_event_log.remove(0);
        }

        // Debug collector puts these events in
        expected_event_log.insert(
            0,
            EventLogEntry::EventWithPayload(EventId::EVENT_LOG_ITEMS_MISSED, 2),
        );
        expected_event_log.push(EventLogEntry::Event(
            EventId::EVENT_PRODUCED_EXTERNAL_REPORT,
        ));

        let report = collector.collect_report().unwrap().unwrap();
        assert_eq!(report.event_log.len(), num_events + 2);

        assert_eq!(
            report,
            Report {
                probe_id,
                probe_clock: lc(probe_id.get_raw(), 0, 0),
                seq_num: SequenceNumber(4),
                frontier_clocks: vec![lc(probe_id.get_raw(), 0, 0)],
                event_log: expected_event_log,
                persistent_epoch_counting: false,
                time_resolution: NanosecondResolution(123),
                wall_clock_id: WallClockId(1),
            }
        );
    }
}
