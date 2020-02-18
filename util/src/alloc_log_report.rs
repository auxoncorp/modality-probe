#[allow(dead_code)]
pub mod lcm {
    include!(concat!(env!("OUT_DIR"), "/log_reporting.rs"));
}

/// Literal materialization of the log_report LCM structure
/// with no semantic enrichment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogReport {
    pub tracer_id: i32,
    pub segments: Vec<LogSegment>,
    pub extension_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Event(i32),
    EventWithMetadata(i32, i32),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LogSegment {
    pub clocks: Vec<Clock>,
    pub events: Vec<Event>,
}

impl LogSegment {
    fn raw_events(&self) -> Vec<i32> {
        self.events
            .iter()
            .fold(Vec::new(), |mut raw_events, event| {
                match event {
                    Event::Event(id) => raw_events.push(*id),
                    Event::EventWithMetadata(id, meta) => {
                        raw_events.push(*id);
                        raw_events.push(*meta);
                    }
                }
                raw_events
            })
    }
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
                    let mut next_meta = (0, false);
                    for event_item_reader in &mut sr {
                        let raw_ev = event_item_reader.read()?;
                        if let (ev, true) = next_meta {
                            segment.events.push(Event::EventWithMetadata(ev, raw_ev));
                            next_meta = (0, false);
                        } else {
                            if (raw_ev & (super::EVENT_WITH_META_MASK as i32))
                                == (super::EVENT_WITH_META_MASK as i32)
                            {
                                next_meta = (raw_ev, true);
                                continue;
                            }
                            segment.events.push(Event::Event(raw_ev));
                        }
                    }
                    Ok(sr.done()?)
                })
                .map_err(|_| ())?;
            segments.push(segment);
        }
        let r = r.done().map_err(|_| ())?;
        let (_n_extension_bytes, r) = r.read_n_extension_bytes().map_err(|_| ())?;
        let (extension_bytes_slice, _read_done_result): (
            _,
            lcm::log_reporting::log_report_read_done<_>,
        ) = r.extension_bytes_as_slice().map_err(|_| ())?;
        let extension_bytes = extension_bytes_slice.to_vec();
        Ok(LogReport {
            tracer_id,
            segments,
            extension_bytes,
        })
    }

    pub fn write_lcm(&self, destination: &mut [u8]) -> Result<usize, ()> {
        let mut buffer_writer = rust_lcm_codec::BufferWriter::new(destination);
        let w = lcm::log_reporting::begin_log_report_write(&mut buffer_writer).map_err(|_| ())?;
        let w = w.write_tracer_id(self.tracer_id).map_err(|_| ())?;

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
                    for (event_item_writer, event) in (&mut sw).zip(segment.raw_events()) {
                        event_item_writer.write(event)?;
                    }
                    Ok(sw.done()?)
                })
                .map_err(|_| ())?;
        }
        let w = w.done().map_err(|_| ())?;
        let w = w
            .write_n_extension_bytes(self.extension_bytes.len() as i32)
            .map_err(|_| ())?;
        let _w: lcm::log_reporting::log_report_write_done<_> = w
            .extension_bytes_copy_from_slice(&self.extension_bytes)
            .map_err(|_| ())?;
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
