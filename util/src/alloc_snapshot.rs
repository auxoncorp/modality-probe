use rust_lcm_codec::{
    BufferReaderError, BufferWriterError, DecodeFingerprintError, DecodeValueError,
    EncodeValueError,
};
use std::convert::TryFrom;
use std::mem::{size_of, size_of_val};
#[allow(dead_code)]
pub mod snapshot_lcm {
    pub use in_system::*;
    include!(concat!(env!("OUT_DIR"), "/snapshot.rs"));
}
use ekotrace::{LogicalClock, TracerId};

#[derive(Debug, PartialEq)]
pub struct OwnedSnapshot {
    pub tracer_id: TracerId,
    pub clocks: Vec<LogicalClock>,
    pub extension_bytes: Vec<u8>,
}

impl OwnedSnapshot {
    pub fn to_lcm_bytes(&self) -> Result<Vec<u8>, SnapshotToLcmError> {
        let mut guessed_size = size_of::<u64>() // expected fingerprint size
            + size_of_val(self)
            + (size_of::<LogicalClock>() * self.clocks.len())
            + self.extension_bytes.len();
        let mut byte_buffer = vec![0u8; guessed_size];
        loop {
            match self.write_to_lcm_byte_buffer(&mut byte_buffer) {
                Ok(n_bytes) => {
                    assert!(n_bytes < byte_buffer.len());
                    byte_buffer.resize(n_bytes, 0u8);
                    return Ok(byte_buffer);
                }
                Err(InnerSnapshotToLcmError::NotEnoughBufferBytes) => {
                    // Double in size each time
                    guessed_size += guessed_size;
                    byte_buffer.clear();
                    byte_buffer.resize(guessed_size, 0u8);
                }
                Err(InnerSnapshotToLcmError::ImplementationLogicError(s)) => {
                    return Err(SnapshotToLcmError::ImplementationLogicError(s))
                }

                Err(InnerSnapshotToLcmError::SnapshotTooBigTooEncode) => {
                    return Err(SnapshotToLcmError::SnapshotTooBigTooEncode)
                }
            }
        }
    }

    fn write_to_lcm_byte_buffer(
        &self,
        buffer: &mut [u8],
    ) -> Result<usize, InnerSnapshotToLcmError> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(buffer);
        {
            let w =
                snapshot_lcm::begin_causal_snapshot_write(&mut buffer_writer).map_err(
                    |e| match e {
                        rust_lcm_codec::EncodeFingerprintError::WriterError(e) => {
                            InnerSnapshotToLcmError::from(e)
                        }
                    },
                )?;
            let w = w.write_tracer_id(self.tracer_id.get_raw() as i32)?;
            let n_clocks = i32::try_from(self.clocks.len())
                .map_err(|_| InnerSnapshotToLcmError::SnapshotTooBigTooEncode)?;
            let mut w = w.write_n_clocks(n_clocks)?;
            for (item_writer, clock) in (&mut w).zip(&self.clocks) {
                item_writer.write(|clock_writer| {
                    let clock_writer = clock_writer.write_tracer_id(clock.id.get_raw() as i32)?;
                    let clock_writer = clock_writer.write_count(clock.count as i32)?;
                    Ok(clock_writer)
                })?
            }
            let w = w.done()?;
            let n_extension_bytes = i32::try_from(self.extension_bytes.len())
                .map_err(|_| InnerSnapshotToLcmError::SnapshotTooBigTooEncode)?;
            let w = w.write_n_extension_bytes(n_extension_bytes)?;
            let _w: snapshot_lcm::causal_snapshot_write_done<_> =
                w.extension_bytes_copy_from_slice(&self.extension_bytes)?;
        }
        Ok(buffer_writer.cursor())
    }

    pub fn from_lcm_bytes(bytes: &[u8]) -> Result<(Self, usize), SnapshotFromLcmError> {
        let mut buffer_reader = rust_lcm_codec::BufferReader::new(bytes);
        let (tracer_id, clocks, extension_bytes) = {
            let r =
                snapshot_lcm::begin_causal_snapshot_read(&mut buffer_reader).map_err(
                    |e| match e {
                        DecodeFingerprintError::InvalidFingerprint(f) => {
                            SnapshotFromLcmError::InvalidFingerprint(f)
                        }
                        DecodeFingerprintError::ReaderError(e) => e.into(),
                    },
                )?;
            let (raw_tracer_id, r) = r.read_tracer_id()?;
            let tracer_id: TracerId = TracerId::try_from(raw_tracer_id as u32).map_err(|_| {
                SnapshotFromLcmError::SemanticallyIncorrectMessage(
                    "tracer_id in message was not a valid ekotrace TracerId".to_string(),
                )
            })?;
            let (n_clocks, mut r) = r.read_n_clocks()?;
            let n_clocks = usize::try_from(n_clocks).map_err(|_| {
                SnapshotFromLcmError::SemanticallyIncorrectMessage(format!(
                    "n_clocks ({})in snapshot was invalid as an array length",
                    n_clocks
                ))
            })?;
            let mut clocks = Vec::with_capacity(n_clocks);
            for item_reader in &mut r {
                let mut maybe_clock_id = None;
                let mut maybe_clock_count = None;
                item_reader.read(|clock_reader| {
                    let (clock_id, clock_reader) = clock_reader.read_tracer_id()?;
                    maybe_clock_id.replace(clock_id);
                    let (clock_count, clock_reader) = clock_reader.read_count()?;
                    maybe_clock_count.replace(clock_count);
                    Ok(clock_reader)
                })?;
                if let (Some(raw_clock_id), Some(raw_clock_count)) =
                    (maybe_clock_id, maybe_clock_count)
                {
                    let id = TracerId::try_from(raw_clock_id as u32).map_err(|_| {
                        SnapshotFromLcmError::SemanticallyIncorrectMessage(
                            "logical clock id in message was not a valid ekotrace TracerId"
                                .to_string(),
                        )
                    })?;
                    let count = raw_clock_count as u32;
                    clocks.push(LogicalClock { id, count });
                } else {
                    return Err(SnapshotFromLcmError::ImplementationLogicError(
                        "Failed to pipe out nested values during logical_clock list reading"
                            .to_string(),
                    ));
                }
            }
            let r = r.done()?;
            if clocks.len() != n_clocks {
                return Err(SnapshotFromLcmError::ImplementationLogicError(
                    "List length mismatch during logical clock interpretation".to_string(),
                ));
            }

            let (n_ext_bytes, r) = r.read_n_extension_bytes()?;
            let n_ext_bytes = usize::try_from(n_ext_bytes).map_err(|_| {
                SnapshotFromLcmError::SemanticallyIncorrectMessage(format!(
                    "n_extension_bytes ({})in snapshot was invalid as an array length",
                    n_ext_bytes
                ))
            })?;
            let mut extension_bytes = Vec::with_capacity(n_ext_bytes);
            // Note the extra type hinting to be sure that the reading affine type chain is exhausted
            let (ext_bytes, _r): (_, snapshot_lcm::causal_snapshot_read_done<_>) =
                r.extension_bytes_as_slice()?;
            extension_bytes.extend_from_slice(ext_bytes);

            (tracer_id, clocks, extension_bytes)
        };

        Ok((
            OwnedSnapshot {
                tracer_id,
                clocks,
                extension_bytes,
            },
            buffer_reader.cursor(),
        ))
    }
}

impl From<BufferReaderError> for SnapshotFromLcmError {
    fn from(_: BufferReaderError) -> Self {
        SnapshotFromLcmError::IncompleteMessage
    }
}

impl From<DecodeValueError<BufferReaderError>> for SnapshotFromLcmError {
    fn from(e: DecodeValueError<BufferReaderError>) -> Self {
        match e {
            DecodeValueError::ArrayLengthMismatch(s) => {
                SnapshotFromLcmError::ImplementationLogicError(format!(
                    "Implementation messed up handling decoding the snapshot array {}",
                    s
                ))
            }
            DecodeValueError::InvalidValue(s) => {
                SnapshotFromLcmError::InvalidMessage(s.to_string())
            }
            DecodeValueError::ReaderError(e) => e.into(),
        }
    }
}

#[derive(Debug)]
pub enum SnapshotFromLcmError {
    InvalidFingerprint(u64),
    IncompleteMessage,
    InvalidMessage(String),
    SemanticallyIncorrectMessage(String),
    ImplementationLogicError(String),
}

impl From<BufferWriterError> for InnerSnapshotToLcmError {
    fn from(_: BufferWriterError) -> Self {
        InnerSnapshotToLcmError::NotEnoughBufferBytes
    }
}

impl From<EncodeValueError<BufferWriterError>> for InnerSnapshotToLcmError {
    fn from(e: EncodeValueError<BufferWriterError>) -> Self {
        match e {
            EncodeValueError::ArrayLengthMismatch(s) => {
                InnerSnapshotToLcmError::ImplementationLogicError(format!(
                    "Implementation messed up handling encoding the snapshot array {}",
                    s
                ))
            }
            EncodeValueError::InvalidValue(s) => InnerSnapshotToLcmError::ImplementationLogicError(
                format!("Implementation messed up handling encoding a value {}", s),
            ),
            EncodeValueError::WriterError(e) => e.into(),
        }
    }
}

#[derive(Debug)]
pub enum SnapshotToLcmError {
    SnapshotTooBigTooEncode,
    ImplementationLogicError(String),
}
#[derive(Debug)]
enum InnerSnapshotToLcmError {
    NotEnoughBufferBytes,
    SnapshotTooBigTooEncode,
    ImplementationLogicError(String),
}

#[cfg(test)]
mod proptest_strategies {
    use super::*;
    use proptest::prelude::*;
    prop_compose! {
        fn extension_bytes(max_length: usize)(vec in prop::collection::vec(proptest::num::u8::ANY, 0..max_length)) -> Vec<u8> {
            vec
        }
    }

    prop_compose! {
        pub(crate) fn raw_tracer_id()(raw_id in 1..=TracerId::MAX_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub(crate) fn tracer_id()(raw_id in raw_tracer_id()) -> TracerId {
            TracerId::try_from(raw_id).unwrap()
        }
    }

    prop_compose! {
        pub(crate) fn logical_clock()(tracer_id in tracer_id(), count in proptest::num::u32::ANY) -> LogicalClock {
            LogicalClock { id: tracer_id, count }
        }
    }

    prop_compose! {
        pub(crate) fn owned_snapshot(max_clocks: usize, max_ext_bytes: usize)(
            tracer_id in tracer_id(),
            clocks in prop::collection::vec(logical_clock(), 0..max_clocks),
            ext_bytes in extension_bytes(max_ext_bytes)
        ) -> OwnedSnapshot {
            OwnedSnapshot {
                tracer_id,
                clocks,
                extension_bytes: ext_bytes,
            }
        }
    }
}
#[cfg(test)]
mod snapshot_tests {
    use super::proptest_strategies::*;
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn round_trip_lcm_snapshots(in_snapshot in owned_snapshot(1025, 513)) {
            let lcm_bytes = in_snapshot.to_lcm_bytes().unwrap();
            let (out_snapshot, bytes_read) = OwnedSnapshot::from_lcm_bytes(&lcm_bytes).unwrap();
            prop_assert_eq!(bytes_read, lcm_bytes.len());
            prop_assert_eq!(in_snapshot, out_snapshot);
        }
    }
}
