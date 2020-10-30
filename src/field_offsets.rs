//! Exposes offsets of ModalityProbe and DynamicHistory fields for
//! use in the debug collector
use crate::{history::DynamicHistory, log::LogEntry, ModalityProbe};
use fenced_ring_buffer::{FencedRingBuffer, SeqNum};
use field_offset::offset_of;

/// Offset of history field in ModalityProbe struct
pub fn history_ptr_offset() -> u64 {
    offset_of!(ModalityProbe => history).get_byte_offset() as u64
}

/// Offset of overwrite_priority field in DynamicHistory struct
pub fn overwrite_priority_offset() -> u64 {
    offset_of!(DynamicHistory => overwrite_priority).get_byte_offset() as u64
}

/// Offset of probe_id field in DynamicHistory struct
pub fn probe_id_offset() -> u64 {
    offset_of!(DynamicHistory => probe_id).get_byte_offset() as u64
}

/// Offset of time_resolution field in DynamicHistory struct
pub fn time_resolution_offset() -> u64 {
    offset_of!(DynamicHistory => time_resolution).get_byte_offset() as u64
}

/// Offset of wall_clock_id field in DynamicHistory struct
pub fn wall_clock_id_offset() -> u64 {
    offset_of!(DynamicHistory => wall_clock_id).get_byte_offset() as u64
}

/// Offset of persistent_epoch_counting field in DynamicHistory struct
pub fn persistent_epoch_counting_offset() -> u64 {
    offset_of!(DynamicHistory => persistent_epoch_counting).get_byte_offset() as u64
}

/// Offset of the high word (u32) of the write sequence number field in DynamicHistory's FencedRingBuffer
pub fn write_seqn_high_offset() -> u64 {
    offset_of!(DynamicHistory => log: FencedRingBuffer<LogEntry> => write_seqn: SeqNum => high)
        .get_byte_offset() as u64
}

/// Offset of the low word (u32) of the write sequence number field in DynamicHistory's FencedRingBuffer
pub fn write_seqn_low_offset() -> u64 {
    offset_of!(DynamicHistory => log: FencedRingBuffer<LogEntry> => write_seqn: SeqNum => low)
        .get_byte_offset() as u64
}

/// Offset of the high word (u32) of the overwrite sequence number field in DynamicHistory's FencedRingBuffer
pub fn overwrite_seqn_high_offset() -> u64 {
    offset_of!(DynamicHistory => log: FencedRingBuffer<LogEntry> => overwrite_seqn: SeqNum => high)
        .get_byte_offset() as u64
}

/// Offset of the low word (u32) of the overwrite sequence number field in DynamicHistory's FencedRingBuffer
pub fn overwrite_seqn_low_offset() -> u64 {
    offset_of!(DynamicHistory => log: FencedRingBuffer<LogEntry> => overwrite_seqn: SeqNum => low)
        .get_byte_offset() as u64
}

/// Offset of the log slice address in DynamicHistory struct
pub fn log_storage_addr_offset() -> u64 {
    offset_of!(DynamicHistory => log: FencedRingBuffer<LogEntry> => storage).get_byte_offset()
        as u64
}

/// Offset of the log slice capacity in DynamicHistory struct.
/// This offset depends on the word size of the target system
pub fn log_storage_cap_offset(n_word_bytes: u8) -> u64 {
    log_storage_addr_offset() + n_word_bytes as u64
}
