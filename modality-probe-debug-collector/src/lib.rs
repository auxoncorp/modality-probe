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
// NOTE: will be used once log processing is implemented
//use core::slice::Iter as SliceIter;
//use core::slice::IterMut as SliceIterMut;

use probe_rs::{MemoryInterface, Session};

// NOTE: will be used once log processing is implemented
//use modality_probe::log_processing::{init_processed_clocks, process_log, LogProcOutput};
use modality_probe::compact_log::CompactLogItem;
use modality_probe::ProbeId;
use modality_probe_udp_collector::add_log_report_to_entries;
use fenced_ring_buffer::reader::{FencedRingBufferReader, Snapper};
use util::alloc_log_report::LogReport;
use util::model::{LogEntry, SegmentId, SessionId};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

// NOTE: These may be changed once FencedRingBuffer is implemented into ekt
// Address offsets of each needed field of the DynamicHistory struct, which is located in modality-probe/src/history.rs
const PROBE_ID_OFFSET: u32 = 0x0;
const WCURS_OFFSET: u32 = 0x4;
const OWCURS_OFFSET: u32 = 0x8;
const LOG_STORAGE_ADDR_OFFSET: u32 = 0xc;
const LOG_STORAGE_CAP_OFFSET: u32 = 0x10;

// NOTE: will be used once log processing is implemented
/*
pub struct LogProcOutputVec<'a, T>(&'a mut Vec<T>);

impl<T, I, M> LogProcOutput<T, I, M> for LogProcOutputVec<'_, T>
where
    I: Iterator<Item = &T>,
    M: Iterator<Item = &mut T>,
{
    fn push(&mut self, item: T) {
        self.0.push(item)
    }

    fn free_capacity(&mut self) -> usize {
        usize::MAX
    }

    fn iter(&mut self) -> SliceIter<'_, T> {
        self.0.iter()
    }

    fn iter_mut(&mut self) -> SliceIterMut<'_, T> {
        self.0.iter_mut()
    }
}*/

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

/// Trait used to specify backend used to access device memory
pub trait MemoryReader {
    fn read32(&mut self, addr: u32) -> Result<u32>;
}

/// MemoryReader that uses probe-rs to access device memory
struct ProbeRsReader(Session);

impl MemoryReader for ProbeRsReader {
    fn read32(&mut self, addr: u32) -> Result<u32> {
        let mut core = self.0.core(0)?;
        Ok(core.read_word_32(addr)?)
    }
}

/// Struct used to take snapshots of FencedRingBuffer on device
struct MemorySnapper {
    /// Reader used to read device memory
    mem_reader: Rc<RefCell<dyn MemoryReader>>,
    /// Address of FencedRingBuffer backing storage
    storage_addr: u32,
    /// Address of FencedRingBuffer write cursor
    wcurs_addr: u32,
    /// Address of FencedRingBuffer overwrite cursor
    owcurs_addr: u32,
}

impl Snapper<CompactLogItem> for MemorySnapper {
    fn snap_wcurs(&self) -> Result<usize> {
        Ok(self.mem_reader.borrow_mut().read32(self.wcurs_addr)? as usize)
    }

    fn snap_owcurs(&self) -> Result<usize> {
        Ok(self.mem_reader.borrow_mut().read32(self.owcurs_addr)? as usize)
    }

    fn snap_storage(&self, index: usize) -> Result<CompactLogItem> {
        let raw: u32 = self
            .mem_reader
            .borrow_mut()
            .read32(self.storage_addr + ((size_of::<CompactLogItem>() * index) as u32))?;
        Ok(CompactLogItem::from_raw(raw))
    }
}

/// Log collector for a single probe
pub struct Collector {
    /// ID of corresponding probe
    id: ProbeId,
    /// Buffer that logs are read into before being processed into a report
    rbuf: Vec<Option<CompactLogItem>>,
    /// Reader used to read the probe's FencedRingBuffer
    reader: FencedRingBufferReader<CompactLogItem, MemorySnapper>,
    // NOTE: will be used once log processing is implemented
    ///// Processed clocks backing storage
    //clocks: Vec<LogicalClock>,
}

impl Collector {
    /// Initialize collector by reading probe information
    pub fn initialize(
        probe_addr: &ProbeAddr,
        mem_reader: Rc<RefCell<dyn MemoryReader>>,
    ) -> Result<Self> {
        let addr = match *probe_addr {
            ProbeAddr::Addr(addr) => addr,
            // Read storage address from pointer
            ProbeAddr::PtrAddr(addr) => mem_reader.borrow_mut().read32(addr)?,
        };
        let mut mem_reader_borrowed = mem_reader.borrow_mut();
        // Get address of DynamicHistory
        let hist_addr = mem_reader_borrowed.read32(addr)?;
        // Read DynamicHistory fields
        let id_raw = mem_reader_borrowed.read32(hist_addr + PROBE_ID_OFFSET)?;
        let id =
            ProbeId::new(id_raw).ok_or_else(|| "Read invalid probe ID from device".to_string())?;
        let buf_addr = mem_reader_borrowed.read32(hist_addr + LOG_STORAGE_ADDR_OFFSET)?;
        let buf_cap = mem_reader_borrowed.read32(hist_addr + LOG_STORAGE_CAP_OFFSET)?;
        let wcurs_addr = hist_addr + WCURS_OFFSET;
        let owcurs_addr = hist_addr + OWCURS_OFFSET;
        drop(mem_reader_borrowed);

        // NOTE: will be used once log processing is implemented
        //let clocks = Vec::new();
        //init_processed_clocks(LogProcOutputVec(&mut clocks), LogicalClock { id, count: 0 });

        Ok(Self {
            id,
            rbuf: Vec::new(),
            reader: FencedRingBufferReader::new(
                MemorySnapper {
                    mem_reader,
                    storage_addr: buf_addr,
                    wcurs_addr,
                    owcurs_addr,
                },
                buf_cap as usize,
            ),
            // NOTE: will be used once log processing is implemented
            //clocks,
        })
    }

    /// Collect all new logs, return a report
    pub fn collect_report(&mut self) -> Result<LogReport> {
        // Perform a FencedRingBuffer read
        self.collect()?;
        let processed_log = Vec::new();

        // NOTE: will be used once log processing is implemented
        /*let num_read = process_log(
            self.rbuf.iter(),
            LogProcOutputVec(&mut self.clocks),
            LogProcOutputVec(&mut processed_log),
        );
        self.rbuf.drain(0..num_read);*/

        match LogReport::try_from_log(self.id, processed_log.into_iter(), &[]) {
            Ok(report) => Ok(report),
            Err(_) => Err("Error creating report".to_string().into()),
        }
    }

    /// Perform a read on the device's FencedRingBuffer
    fn collect(&mut self) -> Result<()> {
        self.reader.read(&mut self.rbuf)
    }

    /// Get reference to read buffer of given collector
    #[cfg(test)]
    pub(crate) fn get_rbuf(&self) -> &Vec<Option<CompactLogItem>> {
        &self.rbuf
    }
}

/// Open memory reader based on config
fn open_memory_reader(c: &Config) -> Result<Rc<RefCell<dyn MemoryReader>>> {
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
fn initialize_collectors(
    c: &Config,
    mem_reader: Rc<RefCell<dyn MemoryReader>>,
) -> Result<Vec<Collector>> {
    let mut collectors = Vec::new();
    for probe_addr in c.probe_addrs.iter() {
        collectors.push(Collector::initialize(probe_addr, mem_reader.clone())?);
    }
    Ok(collectors)
}

/// Write report to given file
fn report_to_file(
    out: &mut File,
    report: LogReport,
    session_id: SessionId,
    include_header_row: bool,
    initial_segment_id: SegmentId,
) -> Result<u32> {
    let mut entries: Vec<LogEntry> = Vec::new();
    let next_segment_id = add_log_report_to_entries(
        &report,
        session_id,
        initial_segment_id,
        Utc::now(),
        &mut entries,
    );
    util::write_csv_log_entries(out, &entries, include_header_row)?;
    Ok(next_segment_id)
}

/// Run debug collector with given config
pub fn run(c: &Config, shutdown_receiver: Receiver<()>) -> Result<()> {
    let mem_reader = open_memory_reader(c)?;
    let mut collectors = initialize_collectors(c, mem_reader)?;

    let mut needs_csv_headers = !c.output_path.exists() || c.output_path.metadata()?.len() == 0;
    let mut out = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&c.output_path)?;

    let mut next_segment_id = 0;
    loop {
        if shutdown_receiver.try_recv().is_ok() {
            break;
        }
        for collector in &mut collectors {
            let report = collector.collect_report()?;
            next_segment_id = report_to_file(
                &mut out,
                report,
                c.session_id,
                needs_csv_headers,
                next_segment_id.into(),
            )?;
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

    use modality_probe::LogicalClock;

    struct HashMapMemReader(HashMap<u32, u32>);

    impl HashMapMemReader {
        const PROBE_PTR_ADDR: u32 = 0x0;
        const PROBE_ADDR: u32 = 0x4;
        const HIST_ADDR: u32 = 0x8;
        const STORAGE_ADDR: u32 = 0x200;

        fn new(
            probe_id: ProbeId,
            wcurs: u32,
            owcurs: u32,
            buf_contents: &Vec<CompactLogItem>,
        ) -> Self {
            let map = hashmap! {
                Self::PROBE_PTR_ADDR => Self::PROBE_ADDR,
                Self::PROBE_ADDR => Self::HIST_ADDR,
                Self::HIST_ADDR + PROBE_ID_OFFSET => probe_id.get().into(),
                Self::HIST_ADDR + LOG_STORAGE_ADDR_OFFSET => Self::STORAGE_ADDR,
                Self::HIST_ADDR + LOG_STORAGE_CAP_OFFSET => buf_contents.len() as u32,
                Self::HIST_ADDR + WCURS_OFFSET => wcurs,
                Self::HIST_ADDR + OWCURS_OFFSET => owcurs
            };
            let mut reader = HashMapMemReader(map);
            reader.overwrite_buffer(&buf_contents);
            reader
        }

        fn overwrite_buffer(&mut self, buf_contents: &Vec<CompactLogItem>) {
            for (index, entry) in buf_contents.iter().enumerate() {
                self.0
                    .insert(Self::STORAGE_ADDR + 4 * (index as u32), entry.raw());
            }
        }

        /*fn set_wcurs(&mut self, new_wcurs: u32) {
            self.0.insert(Self::HIST_ADDR + WCURS_OFFSET, new_wcurs);
        }

        fn set_owcurs(&mut self, new_owcurs: u32) {
            self.0.insert(Self::HIST_ADDR + OWCURS_OFFSET, new_owcurs);
        }*/
    }

    impl MemoryReader for HashMapMemReader {
        fn read32(&mut self, addr: u32) -> Result<u32> {
            Ok(*self.0.get(&addr).unwrap())
        }
    }

    #[test]
    fn initialization_and_retrieval() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            4,
            &mut vec![
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        collector.collect().unwrap();
        assert_eq!(
            &collector.get_rbuf()[..],
            &mut vec![
                Some(
                    CompactLogItem::clock(LogicalClock {
                        id: probe_id,
                        count: 1,
                    })
                    .0
                ),
                Some(
                    CompactLogItem::clock(LogicalClock {
                        id: probe_id,
                        count: 1,
                    })
                    .1
                ),
                Some(CompactLogItem::from_raw(3)),
                Some(CompactLogItem::from_raw(4)),
            ][..]
        )
    }

    /* The following tests require log processing
    /// Create simple report
    #[test]
    fn basic_collection() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();

        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 1
                    }],
                    events: vec![
                        LogEvent::Event(EventId::new(3).unwrap()),
                        LogEvent::Event(EventId::new(4).unwrap()),
                    ]
                }]
            }
        )
    }

    /// Check that local clock is implied at start
    #[test]
    fn no_clocks_available() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    }],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                        LogEvent::Event(EventId::new(3).unwrap()),
                        LogEvent::Event(EventId::new(4).unwrap()),
                    ]
                }]
            }
        )
    }

    /// Put clocks before and after nils at start
    #[test]
    fn nils_at_start() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            6,
            &mut vec![
                CompactLogItem::from_raw(5),
                CompactLogItem::from_raw(6),
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();

        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        }],
                        events: vec![LogEvent::EventWithPayload(EventId::EVENT_LOG_OVERFLOWED, 2)]
                    },
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        }],
                        events: vec![
                            LogEvent::Event(EventId::new(3).unwrap()),
                            LogEvent::Event(EventId::new(4).unwrap()),
                            LogEvent::Event(EventId::new(5).unwrap()),
                            LogEvent::Event(EventId::new(6).unwrap()),
                        ]
                    }
                ]
            }
        )
    }

    /// Put clocks before and after nils at start, even when clocks come after
    #[test]
    fn nils_then_clocks() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            6,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .1,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        }],
                        events: vec![LogEvent::EventWithPayload(EventId::EVENT_LOG_OVERFLOWED, 2)]
                    },
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        }],
                        events: vec![]
                    },
                    OwnedLogSegment {
                        clocks: vec![
                            LogicalClock {
                                id: probe_id,
                                count: 0
                            },
                            LogicalClock {
                                id: other_id,
                                count: 1
                            }
                        ],
                        events: vec![
                            LogEvent::Event(EventId::new(1).unwrap()),
                            LogEvent::Event(EventId::new(2).unwrap()),
                        ]
                    }
                ]
            }
        )
    }

    /// Leave clocks at end in read buffer
    #[test]
    fn clocks_at_end() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    },],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                    ]
                },]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: other_id,
                count: 1,
            })
            .1,
            CompactLogItem::from_raw(3),
            CompactLogItem::from_raw(4),
        ]);
        mem_reader.borrow_mut().set_wcurs(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![
                        LogicalClock {
                            id: probe_id,
                            count: 1
                        },
                        LogicalClock {
                            id: other_id,
                            count: 1
                        },
                    ],
                    events: vec![
                        LogEvent::Event(EventId::new(3).unwrap()),
                        LogEvent::Event(EventId::new(4).unwrap()),
                    ]
                },]
            }
        );
    }

    /// Imply clocks at start of read if not present
    #[test]
    fn imply_multiple_clocks() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            8,
            &mut vec![
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .1,
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![
                        LogicalClock {
                            id: probe_id,
                            count: 1
                        },
                        LogicalClock {
                            id: other_id,
                            count: 1
                        },
                    ],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                        LogEvent::Event(EventId::new(3).unwrap()),
                        LogEvent::Event(EventId::new(4).unwrap()),
                    ]
                },]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::from_raw(5),
            CompactLogItem::from_raw(6),
            CompactLogItem::from_raw(7),
            CompactLogItem::from_raw(8),
            CompactLogItem::from_raw(9),
            CompactLogItem::from_raw(10),
            CompactLogItem::from_raw(11),
            CompactLogItem::from_raw(12),
        ]);
        mem_reader.borrow_mut().set_wcurs(16);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![
                        LogicalClock {
                            id: probe_id,
                            count: 1
                        },
                        LogicalClock {
                            id: other_id,
                            count: 1
                        },
                    ],
                    events: vec![
                        LogEvent::Event(EventId::new(5).unwrap()),
                        LogEvent::Event(EventId::new(6).unwrap()),
                        LogEvent::Event(EventId::new(7).unwrap()),
                        LogEvent::Event(EventId::new(8).unwrap()),
                        LogEvent::Event(EventId::new(9).unwrap()),
                        LogEvent::Event(EventId::new(10).unwrap()),
                        LogEvent::Event(EventId::new(11).unwrap()),
                        LogEvent::Event(EventId::new(12).unwrap()),
                    ]
                },]
            }
        );
    }

    /// Leave clocks at end in read buffer, even if report will be empty
    #[test]
    fn clocks_end_empty_report() {
        let probe_id = ProbeId::new(1).unwrap();
        let other_id = ProbeId::new(2).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .1,
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .0,
                CompactLogItem::clock(LogicalClock {
                    id: other_id,
                    count: 1,
                })
                .1,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::from_raw(1),
            CompactLogItem::from_raw(2),
            CompactLogItem::from_raw(3),
            CompactLogItem::from_raw(4),
        ]);
        mem_reader.borrow_mut().set_wcurs(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![
                        LogicalClock {
                            id: probe_id,
                            count: 1
                        },
                        LogicalClock {
                            id: other_id,
                            count: 1
                        },
                    ],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                        LogEvent::Event(EventId::new(3).unwrap()),
                        LogEvent::Event(EventId::new(4).unwrap()),
                    ]
                },]
            }
        );
    }

    /// Return empty report when no logs read
    #[test]
    fn empty_read() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            0,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::from_raw(3),
                CompactLogItem::from_raw(4),
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![]
            }
        );
    }

    /// Leave nils at end in read buffer
    #[test]
    fn nils_at_end() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::NIL_VAL,
                CompactLogItem::NIL_VAL,
                CompactLogItem::NIL_VAL,
                CompactLogItem::NIL_VAL,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    },],
                    events: vec![]
                }]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .0,
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::from_raw(1),
            CompactLogItem::from_raw(2),
        ]);
        mem_reader.borrow_mut().set_wcurs(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        },],
                        events: vec![LogEvent::EventWithPayload(EventId::EVENT_LOG_OVERFLOWED, 4)]
                    },
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 0
                        },],
                        events: vec![]
                    },
                    OwnedLogSegment {
                        clocks: vec![LogicalClock {
                            id: probe_id,
                            count: 1
                        },],
                        events: vec![
                            LogEvent::Event(EventId::new(1).unwrap()),
                            LogEvent::Event(EventId::new(2).unwrap()),
                        ]
                    },
                ]
            }
        );
    }

    /// Leave clock in read buffer if prefix is last element
    #[test]
    fn split_clock_between_reads() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::from_raw(3),
                CompactLogItem::clock(LogicalClock {
                    id: probe_id,
                    count: 1,
                })
                .0,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    },],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                        LogEvent::Event(EventId::new(3).unwrap()),
                    ]
                }]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::clock(LogicalClock {
                id: probe_id,
                count: 1,
            })
            .1,
            CompactLogItem::from_raw(4),
            CompactLogItem::from_raw(5),
            CompactLogItem::from_raw(6),
        ]);
        mem_reader.borrow_mut().set_wcurs(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 1
                    },],
                    events: vec![
                        LogEvent::Event(EventId::new(4).unwrap()),
                        LogEvent::Event(EventId::new(5).unwrap()),
                        LogEvent::Event(EventId::new(6).unwrap()),
                    ]
                }]
            }
        );
    }

    /// Leave event with payload in read buffer if prefix is last element
    #[test]
    fn split_payload_event_between_reads() {
        let probe_id = ProbeId::new(1).unwrap();
        let mem_reader = Rc::new(RefCell::new(HashMapMemReader::new(
            probe_id,
            4,
            &mut vec![
                CompactLogItem::from_raw(1),
                CompactLogItem::from_raw(2),
                CompactLogItem::from_raw(3),
                CompactLogItem::event_with_payload(EventId::new(4).unwrap(), 5).0,
            ],
        )));

        let mut collector = Collector::initialize(
            &ProbeAddr::Addr(HashMapMemReader::PROBE_ADDR),
            mem_reader.clone() as Rc<RefCell<dyn MemoryReader>>,
        )
        .unwrap();
        let report = collector.collect_report().unwrap();
        assert_eq!(
            report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    },],
                    events: vec![
                        LogEvent::Event(EventId::new(1).unwrap()),
                        LogEvent::Event(EventId::new(2).unwrap()),
                        LogEvent::Event(EventId::new(3).unwrap()),
                    ]
                }]
            }
        );

        mem_reader.borrow_mut().overwrite_buffer(&vec![
            CompactLogItem::event_with_payload(EventId::new(4).unwrap(), 5).1,
            CompactLogItem::from_raw(6),
            CompactLogItem::from_raw(7),
            CompactLogItem::from_raw(8),
        ]);
        mem_reader.borrow_mut().set_wcurs(8);

        let second_report = collector.collect_report().unwrap();
        assert_eq!(
            second_report,
            LogReport {
                probe_id,
                extension_bytes: vec![],
                segments: vec![OwnedLogSegment {
                    clocks: vec![LogicalClock {
                        id: probe_id,
                        count: 0
                    },],
                    events: vec![
                        LogEvent::EventWithPayload(EventId::new(4).unwrap(), 5),
                        LogEvent::Event(EventId::new(6).unwrap()),
                        LogEvent::Event(EventId::new(7).unwrap()),
                        LogEvent::Event(EventId::new(8).unwrap()),
                    ]
                }]
            }
        );
    }*/
}
