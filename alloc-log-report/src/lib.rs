#[allow(dead_code)]
pub mod lcm {
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}

/// Literal materialization of the log_report LCM structure
/// with no semantic enrichment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogReport {
    pub tracer_id: i32,
    pub flags: ErrorFlags,
    pub segments: Vec<LogSegment>,
    pub extension_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ErrorFlags {
    pub has_overflowed_log: bool,
    pub has_overflowed_num_clocks: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LogSegment {
    pub clocks: Vec<Clock>,
    pub events: Vec<i32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clock {
    pub tracer_id: i32,
    pub count: i32,
}

impl LogReport {
    /// Easy mode use of the allocator to fully materialize the log report,
    /// ignoring all the benefits of streamability.
    pub fn from_lcm(bytes: &[u8]) -> Result<LogReport, ()> {
        let mut buffer_reader = rust_lcm_codec::BufferReader::new(bytes);
        let r = lcm::log_reporting::begin_log_report_read(&mut buffer_reader).map_err(|_| ())?;
        let (tracer_id, r) = r.read_tracer_id().map_err(|_| ())?;
        let mut flags = ErrorFlags {
            has_overflowed_log: false,
            has_overflowed_num_clocks: false,
        };
        let r = r
            .read_flags(|fr| {
                let (log_overflow, fr) = fr.read_has_overflowed_log()?;
                flags.has_overflowed_log = log_overflow;
                let (buckets_overflow, fr) = fr.read_has_overflowed_num_clocks()?;
                flags.has_overflowed_num_clocks = buckets_overflow;
                Ok(fr)
            })
            .map_err(|_| ())?;
        let mut segments = Vec::new();
        let (_n_segments, mut r) = r.read_n_segments().map_err(|_| ())?;
        for segment_item_reader in &mut r {
            let mut segment = LogSegment::default();
            segment_item_reader
                .read(|sr| {
                    let (_n_clocks, sr) = sr.read_n_clocks()?;
                    let (_n_events, mut sr) = sr.read_n_events()?;
                    for clock_bucket_item_reader in &mut sr {
                        clock_bucket_item_reader.read(|cbr| {
                            let (id, cbr) = cbr.read_tracer_id()?;
                            let (count, cbr) = cbr.read_count()?;
                            segment.clocks.push(Clock {
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
        let r = r.done().map_err(|_| ())?;
        let (n_extension_bytes, mut r) = r.read_n_extension_bytes().map_err(|_| ())?;
        // N.B. Expect to replace this iteration with cheaper slice-based reading
        // when rust-lcm-codegen is updated to provide special case options for byte arrays.
        let mut extension_bytes = Vec::with_capacity(n_extension_bytes as usize);
        for extension_bytes_item_reader in &mut r {
            extension_bytes.push(extension_bytes_item_reader.read().map_err(|_| ())?);
        }
        let _read_done_result: lcm::log_reporting::log_report_read_done<_> =
            r.done().map_err(|_| ())?;
        Ok(LogReport {
            tracer_id,
            flags,
            segments,
            extension_bytes,
        })
    }

    pub fn write_lcm(&self, destination: &mut [u8]) -> Result<usize, ()> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::log_reporting::begin_log_report_write(&mut buffer_writer).map_err(|_| ())?;
        let w = w.write_tracer_id(self.tracer_id).map_err(|_| ())?;
        let w = w
            .write_flags(|fw| {
                let fw = fw.write_has_overflowed_log(self.flags.has_overflowed_log)?;
                let fw =
                    fw.write_has_overflowed_num_clocks(self.flags.has_overflowed_num_clocks)?;
                Ok(fw)
            })
            .map_err(|_| ())?;

        let expected_n_segments = self.segments.len();
        let mut w = w
            .write_n_segments(expected_n_segments as i32)
            .map_err(|_| ())?;
        for (segment_item_writer, segment) in (&mut w).zip(&self.segments) {
            segment_item_writer
                .write(|sw| {
                    let sw = sw.write_n_clocks(segment.clocks.len() as i32)?;
                    let mut sw = sw.write_n_events(segment.events.len() as i32)?;
                    for (bucket_item_writer, bucket) in (&mut sw).zip(&segment.clocks) {
                        bucket_item_writer.write(|bw| {
                            Ok(bw
                                .write_tracer_id(bucket.tracer_id)?
                                .write_count(bucket.count)?)
                        })?;
                    }
                    let mut sw = sw.done()?;
                    for (event_item_writer, event) in (&mut sw).zip(&segment.events) {
                        event_item_writer.write(*event)?;
                    }
                    Ok(sw.done()?)
                })
                .map_err(|_| ())?;
        }
        let w = w.done().map_err(|_| ())?;
        let mut w = w
            .write_n_extension_bytes(self.extension_bytes.len() as i32)
            .map_err(|_| ())?;
        // N.B. Expect to replace this iteration with cheaper slice-based copying
        // when rust-lcm-codegen is updated to provide special case options for byte arrays.
        for (extension_byte_item_writer, extension_byte) in (&mut w).zip(&self.extension_bytes) {
            extension_byte_item_writer
                .write(*extension_byte)
                .map_err(|_| ())?;
        }
        let _w: lcm::log_reporting::log_report_write_done<_> = w.done().map_err(|_| ())?;
        Ok(buffer_writer.cursor())
    }
}
#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
