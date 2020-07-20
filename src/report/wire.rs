//! This module contains the on-the-wire model for reports and its
//! serialization and deserialization.
use crate::{
    compact_log::{CompactLogItem, LogEvent, LogItem, LogItemInterpretationError, LogItemIterator},
    report::bulk::{self, BulkReportSourceComponents, BulkReporter},
    wire::BulkReportWireError,
    ExtensionBytes, LogicalClock, ProbeId, ReportError,
};

/// An on-the-wire log report.
#[derive(Clone, Debug, PartialEq)]
pub struct LogReport {
    /// The id of the probe that sent this report.
    pub probe_id: ProbeId,
    /// The segements contained in this report.
    pub segments: Vec<OwnedLogSegment>,
    /// Opaque to include aribtrary context with a report.
    pub extension_bytes: Vec<u8>,
}

/// A segment is an ordered chunk of events marked by a specific
/// (local) clock value.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct OwnedLogSegment {
    /// The local clock and any probes' clocks that were involved in
    /// interactions with the local probe.
    pub clocks: Vec<LogicalClock>,
    /// The ordered events that were recorded with the local probe
    /// while the clocks had the values above.
    pub events: Vec<LogEvent>,
}

impl LogReport {
    #[inline]
    /// Build a report from the compact representation.
    pub fn try_from_log(
        probe_id: ProbeId,
        log: impl Iterator<Item = CompactLogItem>,
        extension_bytes: &[u8],
    ) -> Result<Self, LogItemInterpretationError> {
        let mut segments = Vec::new();
        let mut curr_segment = None;
        for item_result in LogItemIterator::new(log) {
            let item = item_result?;
            match item {
                LogItem::Clock(clock) => {
                    // Use the source probe id to distinguish between contiguous segments
                    // consisting only of clocks
                    if clock.id == probe_id {
                        if let Some(prior_segment) = curr_segment.replace(OwnedLogSegment {
                            clocks: vec![clock],
                            events: vec![],
                        }) {
                            segments.push(prior_segment);
                        }
                    } else if let Some(segment) = curr_segment.as_mut() {
                        segment.clocks.push(clock)
                    } else {
                        curr_segment = Some(OwnedLogSegment {
                            clocks: vec![clock],
                            events: vec![],
                        });
                    }
                }
                LogItem::LogEvent(event) => {
                    if let Some(segment) = curr_segment.as_mut() {
                        segment.events.push(event);
                    } else {
                        curr_segment = Some(OwnedLogSegment {
                            clocks: vec![],
                            events: vec![event],
                        })
                    }
                }
            }
        }
        if let Some(last_segment) = curr_segment {
            segments.push(last_segment);
        }
        Ok(LogReport {
            probe_id,
            segments,
            extension_bytes: Vec::from(extension_bytes),
        })
    }

    /// Hydrate a report from wire-based bytes.
    pub fn try_from_bulk_bytes(bytes: &[u8]) -> Result<Self, ParseBulkReportError> {
        let (probe, log_iter, ext_bytes) = bulk::try_bulk_from_wire_bytes(bytes)
            .map_err(ParseBulkReportError::ParseBulkFromWire)?;
        LogReport::try_from_log(probe, log_iter, ext_bytes.0)
            .map_err(ParseBulkReportError::CompactLogInterpretation)
    }

    /// Write the report as bytes to `destination`.
    pub fn write_bulk_bytes(&self, destination: &mut [u8]) -> Result<usize, ReportError> {
        let mut log = Vec::with_capacity(
            self.segments
                .iter()
                .map(|s| 2 * (s.clocks.len() + s.events.len()))
                .sum(),
        );
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
            probe_id: self.probe_id,
            log: &log,
        }
        .report_with_extension(destination, ExtensionBytes(&self.extension_bytes))
    }
}

/// The error returned when deserializing a wire-formatted report to a
/// `LogReport`.
#[derive(Debug)]
pub enum ParseBulkReportError {
    /// Parsing the wire format failed.
    ParseBulkFromWire(BulkReportWireError),
    /// Parsing was successful, but the resulting report was broken.
    CompactLogInterpretation(LogItemInterpretationError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EventId, LogicalClock, ProbeEpoch, ProbeId, ProbeTicks};
    use proptest::prelude::*;
    use std::convert::TryInto;

    #[test]
    fn round_trip_report() {
        let tid_a = 10.try_into().unwrap();
        let tid_b = 15.try_into().unwrap();
        let input_report = LogReport {
            probe_id: tid_a,
            segments: vec![OwnedLogSegment {
                clocks: vec![
                    LogicalClock {
                        id: tid_a,
                        epoch: 0,
                        ticks: 1,
                    },
                    LogicalClock {
                        id: tid_b,
                        epoch: 0,
                        ticks: 200,
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
        pub(crate) fn gen_raw_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        fn gen_clock()(probe_id in gen_raw_probe_id(),
                       epoch in gen_probe_epoch(),
                       ticks in gen_probe_ticks()
        ) -> LogicalClock {
            LogicalClock { id: probe_id.try_into().unwrap(), epoch, ticks }
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_internal_event_id()(raw_id in (EventId::MAX_USER_ID + 1)..EventId::MAX_INTERNAL_ID) -> u32 {
            raw_id
        }
    }

    pub(crate) fn gen_probe_epoch() -> impl Strategy<Value = ProbeEpoch> {
        any::<u16>()
    }

    pub(crate) fn gen_probe_ticks() -> impl Strategy<Value = ProbeTicks> {
        any::<u16>()
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
        pub(crate) fn arb_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> ProbeId {
            ProbeId::new(raw_id).unwrap()
        }
    }

    prop_compose! {
        fn gen_log_report()
            (probe_id in arb_probe_id(), mut segments in gen_segments(25), extension_bytes in gen_extension_bytes(200)) -> LogReport {
            let mut fixup_count = 0;
            for segment in segments.iter_mut() {
                let needs_first_clock_id_fixup = if let Some(first_clock) = segment.clocks.first() {
                    first_clock.id != probe_id
                } else {
                    true
                };
                // Our segmentation logic depends on the first clock probe of each segment
                // matching the id of the probe where the log report was generated
                if needs_first_clock_id_fixup {
                    fixup_count += 1;
                    segment.clocks.insert(0, LogicalClock { id: probe_id, epoch: 0, ticks: fixup_count })
                }
            }
            LogReport {
                probe_id,
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
