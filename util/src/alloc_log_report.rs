use super::EVENT_WITH_PAYLOAD_MASK;
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
    EventWithPayload(i32, i32),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LogSegment {
    pub clocks: Vec<Clock>,
    pub events: Vec<Event>,
}

impl LogSegment {
    /// Represent the events in the compact-log format
    fn raw_compact_events(&self) -> Vec<i32> {
        self.events
            .iter()
            .fold(Vec::new(), |mut raw_events, event| {
                match event {
                    Event::Event(id) => raw_events.push(*id),
                    Event::EventWithPayload(id, payload) => {
                        raw_events.push(((*id as u32) | EVENT_WITH_PAYLOAD_MASK) as i32);
                        raw_events.push(*payload);
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
                    let mut event_expecting_payload = None;
                    for event_item_reader in &mut sr {
                        let raw_ev = event_item_reader.read()? as u32;
                        if let Some(ev) = event_expecting_payload.take() {
                            segment
                                .events
                                .push(Event::EventWithPayload(ev as i32, raw_ev as i32));
                        } else if raw_ev & EVENT_WITH_PAYLOAD_MASK == EVENT_WITH_PAYLOAD_MASK {
                            event_expecting_payload = Some(raw_ev & !EVENT_WITH_PAYLOAD_MASK)
                        } else {
                            segment.events.push(Event::Event(raw_ev as i32));
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
                    let raw_events = segment.raw_compact_events();
                    let mut sw = sw.write_n_events(raw_events.len() as i32)?;
                    for (bucket_item_writer, bucket) in (&mut sw).zip(&segment.clocks) {
                        bucket_item_writer.write(|bw| {
                            Ok(bw
                                .write_tracer_id(bucket.tracer_id)?
                                .write_count(bucket.count)?)
                        })?;
                    }
                    let mut sw = sw.done()?;
                    for (event_item_writer, event) in (&mut sw).zip(raw_events) {
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
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn round_trip_report() {
        let tid_a = 10;
        let tid_b = 15;
        let input_report = LogReport {
            tracer_id: tid_a,
            segments: vec![LogSegment {
                clocks: vec![
                    Clock {
                        tracer_id: tid_a,
                        count: 1,
                    },
                    Clock {
                        tracer_id: tid_b,
                        count: 200,
                    },
                ],
                events: vec![
                    Event::Event(3),
                    Event::EventWithPayload(1, 4),
                    Event::EventWithPayload(5, 1),
                    Event::Event(2),
                ],
            }],
            extension_bytes: vec![1, 2, 3, 9, 8, 7],
        };

        let mut buffer = vec![0u8; 1024];
        let n_bytes = input_report.write_lcm(&mut buffer).unwrap();

        let output_report = LogReport::from_lcm(&buffer[..n_bytes]).unwrap();

        assert_eq!(input_report, output_report);
    }

    prop_compose! {
        fn gen_extension_bytes(max_length: usize)(vec in prop::collection::vec(proptest::num::u8::ANY, 0..max_length)) -> Vec<u8> {
            vec
        }
    }

    prop_compose! {
        fn gen_clock()(tracer_id in 1..2000, count in proptest::num::i32::ANY) -> Clock {
            Clock { tracer_id, count }
        }
    }

    prop_compose! {
        fn gen_event()(has_payload in proptest::bool::ANY, event_id in 1..std::i16::MAX, payload in proptest::num::i32::ANY) -> Event {
            if has_payload {
                Event::EventWithPayload(event_id as i32, payload)
            } else {
                Event::Event(event_id as i32)
            }
        }
    }

    prop_compose! {
        fn gen_segment(max_clocks: usize, max_events: usize)
            (clocks in prop::collection::vec(gen_clock(), 0..max_clocks),
                events in prop::collection::vec(gen_event(), 0..max_events)) -> LogSegment {
            LogSegment {
                clocks,
                events,
            }
        }
    }

    prop_compose! {
        fn gen_segments(max_length: usize)(vec in prop::collection::vec(gen_segment(100, 258), 0..max_length)) -> Vec<LogSegment> {
            vec
        }
    }

    prop_compose! {
        fn gen_log_report()
            (tracer_id in 1i32..1000, segments in gen_segments(257), extension_bytes in gen_extension_bytes(200)) -> LogReport {
            LogReport {
                tracer_id,
                segments,
                extension_bytes,
            }
        }
    }

    proptest! {
        #[test]
        fn generative_round_trip_log_report(input_report in gen_log_report()) {
            const MEGABYTE: usize = 1024*1024;
            let mut buffer = vec![0u8; MEGABYTE];
            let n_bytes = input_report.write_lcm(&mut buffer).unwrap();
            let output_report = LogReport::from_lcm(&buffer[..n_bytes]).unwrap();
            assert_eq!(input_report, output_report);
        }
    }
}
