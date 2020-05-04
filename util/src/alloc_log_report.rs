use ekotrace::compact_log::{CompactLogItem, LogEvent};
use ekotrace::{BulkReporter, ExtensionBytes, ReportError};

/// Literal materialization of the log_report LCM structure
/// with no semantic enrichment.
#[derive(Clone, Debug, PartialEq)]
pub struct LogReport {
    pub tracer_id: ekotrace::TracerId,
    pub segments: Vec<OwnedLogSegment>,
    pub extension_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct OwnedLogSegment {
    pub clocks: Vec<ekotrace::LogicalClock>,
    pub events: Vec<LogEvent>,
}

impl LogReport {
    pub fn try_from_log(
        tracer_id: ekotrace::TracerId,
        log: &[ekotrace::compact_log::CompactLogItem],
        extension_bytes: &[u8],
    ) -> Result<Self, ekotrace::compact_log::LogEventInterpretationError> {
        let mut segments = Vec::new();
        for segment in ekotrace::compact_log::LogSegmentIterator::new(tracer_id, log) {
            let mut events = Vec::new();
            for event_result in segment.iter_events() {
                events.push(event_result?);
            }
            segments.push(OwnedLogSegment {
                clocks: segment.iter_clocks().collect(),
                events,
            })
        }
        Ok(LogReport {
            tracer_id,
            segments,
            extension_bytes: Vec::from(extension_bytes),
        })
    }

    pub fn try_from_bulk_bytes(bytes: &[u8]) -> Result<Self, ParseBulkReportError> {
        let (location, log_bytes, ext_bytes) =
            ekotrace::report::bulk::try_bulk_from_wire_bytes(bytes)
                .map_err(|e| ParseBulkReportError::ParseBulkFromWire(e))?;
        let mut log = Vec::with_capacity(
            log_bytes.len() / std::mem::size_of::<ekotrace::compact_log::CompactLogItem>(),
        );
        for item_bytes in log_bytes.chunks_exact(4) {
            log.push(CompactLogItem::from_raw(u32::from_le_bytes([
                item_bytes[0],
                item_bytes[1],
                item_bytes[2],
                item_bytes[3],
            ])))
        }
        LogReport::try_from_log(location, &log, ext_bytes.0)
            .map_err(|e| ParseBulkReportError::CompactLogInterpretation(e))
    }

    pub fn write_bulk_bytes(&self, destination: &mut [u8]) -> Result<usize, ReportError> {
        use ekotrace::report::bulk::BulkReportSourceComponents;
        let mut log = Vec::new();
        for segment in &self.segments {
            for clock in &segment.clocks {
                let (id, count) = CompactLogItem::clock(*clock);
                log.push(id);
                log.push(count);
            }
            for log_event in &segment.events {
                match log_event {
                    LogEvent::Event(id) => log.push(CompactLogItem::event(*id)),
                    LogEvent::EventWithPayload(id, payload) => {
                        let (id, payload) = CompactLogItem::event_with_payload(*id, *payload);
                        log.push(id);
                        log.push(payload);
                    }
                }
            }
        }

        BulkReportSourceComponents {
            location_id: self.tracer_id,
            log: &log,
        }
        .report_with_extension(destination, ExtensionBytes(&self.extension_bytes))
    }
}

#[derive(Debug)]
pub enum ParseBulkReportError {
    ParseBulkFromWire(ekotrace::report::bulk::ParseBulkFromWireError),
    CompactLogInterpretation(ekotrace::compact_log::LogEventInterpretationError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use ekotrace::{EventId, LogicalClock, TracerId};
    use proptest::prelude::*;
    use std::convert::TryInto;

    #[test]
    fn round_trip_report() {
        let tid_a = 10.try_into().unwrap();
        let tid_b = 15.try_into().unwrap();
        let input_report = LogReport {
            tracer_id: tid_a,
            segments: vec![OwnedLogSegment {
                clocks: vec![
                    LogicalClock {
                        id: tid_a,
                        count: 1,
                    },
                    LogicalClock {
                        id: tid_b,
                        count: 200,
                    },
                ],
                events: vec![
                    LogEvent::Event(3.try_into().unwrap()),
                    LogEvent::EventWithPayload(1.try_into().unwrap(), 4),
                    LogEvent::EventWithPayload(5.try_into().unwrap(), 1),
                    LogEvent::Event(2.try_into().unwrap()),
                ],
            }],
            extension_bytes: vec![1, 2, 3, 9, 8, 7],
        };

        let mut buffer = vec![0u8; 1024];
        let n_bytes = input_report.write_bulk_bytes(&mut buffer).unwrap();

        let output_report = LogReport::try_from_bulk_bytes(&buffer[..n_bytes]).unwrap();

        assert_eq!(input_report, output_report);
    }

    prop_compose! {
        fn gen_extension_bytes(max_length: usize)(vec in prop::collection::vec(proptest::num::u8::ANY, 0..max_length)) -> Vec<u8> {
            vec
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_tracer_id()(raw_id in 1..=TracerId::MAX_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        fn gen_clock()(tracer_id in gen_raw_tracer_id(), count in proptest::num::u32::ANY) -> LogicalClock {
            LogicalClock { id: tracer_id.try_into().unwrap(), count }
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_internal_event_id()(raw_id in (EventId::MAX_USER_ID + 1)..EventId::MAX_INTERNAL_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
            raw_id
        }
    }

    fn gen_event() -> impl Strategy<Value = LogEvent> {
        prop_oneof![
            gen_raw_internal_event_id()
                .prop_map(|id| LogEvent::Event(EventId::new_internal(id).unwrap())),
            (gen_raw_internal_event_id(), any::<u32>()).prop_map(|(id, payload)| {
                LogEvent::EventWithPayload(EventId::new_internal(id).unwrap(), payload)
            }),
            gen_raw_user_event_id().prop_map(|id| LogEvent::Event(EventId::new(id).unwrap())),
            (gen_raw_user_event_id(), any::<u32>()).prop_map(|(id, payload)| {
                LogEvent::EventWithPayload(EventId::new(id).unwrap(), payload)
            }),
        ]
    }

    prop_compose! {
        fn gen_segment(max_clocks: usize, max_events: usize)
            (clocks in prop::collection::vec(gen_clock(), 1..max_clocks),
                events in prop::collection::vec(gen_event(), 1..max_events)) -> OwnedLogSegment {
            OwnedLogSegment {
                clocks,
                events,
            }
        }
    }

    prop_compose! {
        fn gen_segments(max_length: usize)(vec in prop::collection::vec(gen_segment(100, 258), 0..max_length)) -> Vec<OwnedLogSegment> {
            vec
        }
    }

    prop_compose! {
        pub(crate) fn arb_tracer_id()(raw_id in 1..=TracerId::MAX_ID) -> TracerId {
            TracerId::new(raw_id).unwrap()
        }
    }

    prop_compose! {
        fn gen_log_report()
            (tracer_id in arb_tracer_id(), segments in gen_segments(257), extension_bytes in gen_extension_bytes(200)) -> LogReport {
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
            let n_bytes = input_report.write_bulk_bytes(&mut buffer).unwrap();
            let output_report = LogReport::try_from_bulk_bytes(&buffer[..n_bytes]).unwrap();
            assert_eq!(input_report, output_report);
        }
    }
}
