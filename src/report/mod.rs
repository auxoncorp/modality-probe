//! Facilities relating to the encoding and decoding of
//! Modality probe reports.  Reports are detailed event and
//! causality data messages that should be sent to an
//! analysis or collection service.
use core::mem::{align_of, size_of};

use static_assertions::{assert_eq_align, assert_eq_size};

use crate::{log::LogEntry, ReportError};

/// Returns an error if the provided log could not fit into the
/// destination bytes
pub(crate) fn write_log_as_little_endian_bytes(
    destination: &mut [u8],
    log: &[LogEntry],
) -> Result<(), ReportError> {
    if destination.len() / size_of::<LogEntry>() < log.len() {
        return Err(ReportError::InsufficientDestinationSize);
    }
    // If the alignment is correct, do easy word overlay with fast copy operations
    if destination.as_ptr() as usize % align_of::<LogEntry>() == 0 {
        if cfg!(target_endian = "little") {
            assert_eq_align!(u32, LogEntry);
            assert_eq_size!(u32, LogEntry);
            // Specifically checked for alignment directly above
            #[allow(clippy::cast_ptr_alignment)]
            let destination_words_exact: &mut [u32] = unsafe {
                core::slice::from_raw_parts_mut(destination.as_mut_ptr() as *mut u32, log.len())
            };
            destination_words_exact.copy_from_slice(unsafe {
                // Safe to do this sort of slice reinterpretation because LogEntry
                // is repr(transparent) and backed by a u32. Since the cfg check above
                // demonstrates that the endian-ness of the wire format and the current device
                // line up, no further conversion is necessary.
                core::slice::from_raw_parts(log.as_ptr() as *const u32, log.len())
            })
        } else {
            // If the destination buffer is well-aligned, but the device is the wrong endianness
            // do things the hard way
            for (item, four_byte_dest_slice) in log
                .iter()
                .zip(destination.chunks_exact_mut(size_of::<LogEntry>()))
            {
                four_byte_dest_slice.copy_from_slice(&item.raw().to_le_bytes());
            }
        }
    } else {
        // If the destination buffer is not well-aligned, do things the hard way.
        for (item, four_byte_dest_slice) in log
            .iter()
            .zip(destination.chunks_exact_mut(size_of::<LogEntry>()))
        {
            four_byte_dest_slice.copy_from_slice(&item.raw().to_le_bytes());
        }
    }
    Ok(())
}
