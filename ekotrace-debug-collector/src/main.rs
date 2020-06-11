use std::env;
use std::error::Error;
use std::fs::File;
use std::io::prelude::*;
use std::str;

use probe_rs::Probe;

use ekotrace::compact_log::CompactLogItem;
use ekotrace::{EventId, LogicalClock, TracerId};
use ekotrace_udp_collector::add_log_report_to_entries;
use goblin::elf::Elf;
use util::{alloc_log_report::LogReport, model::LogEntry, model::SegmentId, model::SessionId};

use chrono::{DateTime, Utc};
use race_buffer::RaceBufferReader;
use std::time::Duration;
use std::time::SystemTime;

struct offsets {
    tracer_id: u64,
    event_count: u64,
    clocks_addr: u64,
    clocks_len: u64,
    log_addr: u64,
    log_len: u64,
}

const offsets_16: offsets = offsets {
    tracer_id: 0x0,
    event_count: 0x4,
    clocks_addr: 0xE,
    clocks_len: 0x12,
    log_addr: 0x14,
    log_len: 0x18,
};

const offsets_32: offsets = offsets {
    tracer_id: 0x0,
    event_count: 0x4,
    clocks_addr: 0x10,
    clocks_len: 0x18,
    log_addr: 0x1c,
    log_len: 0x24,
};

const offsets_64: offsets = offsets {
    tracer_id: 0x0,
    event_count: 0x4,
    clocks_addr: 0x14,
    clocks_len: 0x24,
    log_addr: 0x2c,
    log_len: 0x3c,
};

fn main() {
    let args: Vec<String> = env::args().collect();
    let sym_path = &(args[1]);
    let log_label = &(args[2]);
    let _out_path = &(args[3]);

    let mut elf_buf = Vec::new();
    let mut elf_file = open_elf(sym_path, &mut elf_buf).unwrap();
    let (log_addr_64, _) = parse_symbol_info(&mut elf_file, log_label).unwrap();
    let tracer_pointer_addr = log_addr_64 as u32;

    let probes = Probe::list_all();
    let probe = probes[0].open().expect("Probe open cannot fail");
    // Attach to a chip.
    let session = probe.attach("stm32").expect("Probe attach cannot fail");
    // Select a core.
    let core = session
        .attach_to_core(0)
        .expect("Attach to core cannot fail");
    //core.halt().unwrap();

    let buf_addr =  core.read_word_32(tracer_pointer_addr).unwrap();
    let storage_addr = core.read_word_32(buf_addr + 4).unwrap();
    let storage_size = core.read_word_32(buf_addr + 8).unwrap() as usize;
    let mut rbuf = Vec::new();
    let mut reader = RaceBufferReader::new(
        storage_size,
        || unsafe { core.read_word_32(buf_addr).unwrap() as usize},
        |i| unsafe { core.read_word_32(storage_addr + 4 * (i as u32)).unwrap() },
        |_| false,
        0,
    );
    
    for _ in 0..100 {
        reader.read(&mut rbuf);
        std::thread::sleep(Duration::from_millis(80));
    }
    for v in &rbuf {
        println!("val: {}", v);
    }
    assert!(is_correct_order(&rbuf[..]));
    /*
    // Read in log
    let tracer_addr = core.read_word_32(tracer_pointer_addr).unwrap();
    let hist_addr = core.read_word_32(tracer_addr).unwrap();
    let tracer_id_raw = core.read_word_32(hist_addr).unwrap();
    let tracer_id = TracerId::new(tracer_id_raw).unwrap();
    let _event_count = core.read_word_32(hist_addr + 0x4).unwrap();

    let clocks_addr = core.read_word_32(hist_addr + 0x10).unwrap();
    let clocks_len = core.read_word_32(hist_addr + 0x18).unwrap();

    let log_addr = core.read_word_32(hist_addr + 0x1c).unwrap();
    let log_len = core.read_word_32(hist_addr + 0x24).unwrap();

    let mut clocks = Vec::new();
    for i in 0..clocks_len {
        let clock_id_raw = core.read_word_32(clocks_addr + 8 * i).unwrap();
        let clock_count = core.read_word_32(clocks_addr + 8 * i + 4).unwrap();
        let clock_id = TracerId::new(clock_id_raw).unwrap();
        clocks.push(LogicalClock {
            id: clock_id,
            count: clock_count,
        });
    }

    let mut log = Vec::new();
    for i in 0..log_len {
        let log_item_raw = core.read_word_32(log_addr + 4 * i).unwrap();
        log.push(CompactLogItem::from_raw(log_item_raw));
    }

    // print()
    println!("Clocks");
    for c in clocks.iter() {
        print!("{}, {}; ", c.id.get_raw(), c.count);
    }
    println!("");
    println!("Log:");
    let mut next_clock_count = false;
    for l in log.iter() {
        if next_clock_count {
            print!("Count: {}], ", l.raw());
            next_clock_count = false;
        } else {
            if l.has_clock_bit_set() {
                print!("[ID: {} ", l.interpret_as_logical_clock_tracer_id());
                next_clock_count = true;
            } else {
                print!("{}, ", l.raw());
            }
        }
    }
    println!("");

    // finished report logging
    // increment local clock
    clocks[0].count = clocks[0].count.saturating_add(1);
    core.write_word_32(clocks_addr + 4, clocks[0].count);
    // log clocks
    let mut new_log = Vec::new();
    for c in clocks.iter() {
        let (id, count) = CompactLogItem::clock(*c);
        new_log.push(id.raw());
        new_log.push(count.raw());
    }
    // log report created event
    new_log.push(EventId::EVENT_PRODUCED_EXTERNAL_REPORT.get_raw());
    let num_entries = new_log.len();
    // pad 0s to overwrite
    for i in 0..(log.len() - num_entries) {
        new_log.push(0);
    }
    core.write_word_32(hist_addr + 0x24, num_entries as u32).unwrap();
    core.write_32(log_addr, &new_log[..]).unwrap();
    core.run().unwrap();

    // write to csv
    let report = LogReport::try_from_log(tracer_id, log.into_iter(), &[]).unwrap();
    let mut entries: Vec<LogEntry> = Vec::new();
    add_log_report_to_entries(&report, SessionId::from(0), SegmentId::from(0),
        Utc::now(), &mut entries);
    let mut out = File::create("out").unwrap();
    util::write_csv_log_entries(&mut out, &entries, true).unwrap();*/
}

fn is_correct_order(rbuf: &[u32]) -> bool {
    for i in 0..rbuf.len() {
        if rbuf[i] != i as u32 + 1 && rbuf[i] != 0 {
            return false;
        }
    }
    return true;
}

fn parse_symbol_info(elf_file: &mut Elf, log_label: &str) -> Option<(u64, u64)> {
    let log_sym = elf_file.syms.iter().find(|sym| -> bool {
        let name_opt = elf_file.strtab.get(sym.st_name);
        if let Some(name_res) = name_opt {
            if let Ok(name) = name_res {
                return name == log_label;
            }
        }
        return false;
    })?;
    Some((log_sym.st_value, log_sym.st_size))
}

fn open_elf<'a>(path: &str, elf_buf: &'a mut Vec<u8>) -> Result<Box<Elf<'a>>, Box<dyn Error>> {
    let mut file = File::open(path)?;
    file.read_to_end(elf_buf)?;
    match Elf::parse(elf_buf) {
        Ok(elf) => Ok(Box::new(elf)),
        Err(err) => Err(Box::new(err)),
    }
}
