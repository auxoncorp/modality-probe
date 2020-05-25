use chrono::prelude::*;
use itertools::Itertools;
use petgraph::graph::Graph;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::{TryFrom, TryInto};
use std::io::{Read, Write};

pub mod alloc_log_report;
pub mod model;

/// Serialization record for CSV storage
#[derive(Debug, serde::Serialize, serde::Deserialize, Eq, PartialEq)]
struct LogFileLine {
    session_id: u32,
    segment_id: u32,
    segment_index: u32,
    receive_time: DateTime<Utc>,
    tracer_id: u32,
    event_id: Option<u32>,
    event_payload: Option<u32>,
    lc_tracer_id: Option<u32>,
    lc_clock: Option<u32>,
}

impl From<&model::LogEntry> for LogFileLine {
    fn from(e: &model::LogEntry) -> LogFileLine {
        LogFileLine {
            session_id: e.session_id.0,
            segment_id: e.segment_id.0,
            segment_index: e.segment_index,
            tracer_id: e.tracer_id.get_raw(),
            event_id: match &e.data {
                model::LogEntryData::Event(id) => Some(id.get_raw()),
                model::LogEntryData::EventWithPayload(id, _) => Some(id.get_raw()),
                _ => None,
            },
            event_payload: match &e.data {
                model::LogEntryData::EventWithPayload(_, payload) => Some(*payload),
                _ => None,
            },
            lc_tracer_id: match &e.data {
                model::LogEntryData::LogicalClock(tracer_id, _) => Some(tracer_id.get_raw()),
                _ => None,
            },
            lc_clock: match &e.data {
                model::LogEntryData::LogicalClock(_, clock) => Some(*clock),
                _ => None,
            },
            receive_time: e.receive_time,
        }
    }
}

impl TryFrom<&LogFileLine> for model::LogEntry {
    type Error = ReadError;

    fn try_from(l: &LogFileLine) -> Result<model::LogEntry, Self::Error> {
        let session_id: model::SessionId = l.session_id.into();
        let segment_id: model::SegmentId = l.segment_id.into();
        let segment_index: u32 = l.segment_index;

        let data = if let Some(event_id) = l.event_id {
            if l.lc_tracer_id.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When event_id is present, lc_tracer_id must be empty",
                });
            } else if l.lc_clock.is_some() {
                return Err(ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When event_id is present, lc_clock must be empty",
                });
            }

            let event_id = event_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "Invalid event id",
                })?;
            if let Some(payload) = l.event_payload {
                model::LogEntryData::EventWithPayload(event_id, payload)
            } else {
                model::LogEntryData::Event(event_id)
            }
        } else if let Some(lc_tracer_id) = l.lc_tracer_id {
            match l.lc_clock {
                None => {
                    return Err(ReadError::InvalidContent {
                        session_id,
                        segment_id,
                        segment_index,
                        message: "When lc_tracer_id is present, lc_clock must also be present",
                    });
                }
                Some(lc_clock) => model::LogEntryData::LogicalClock(lc_tracer_id.try_into().map_err(|_e|
                    ReadError::InvalidContent {
                        session_id,
                        segment_id,
                        segment_index,
                        message: "When lc_tracer_id is present, it must be a valid ekotrac::TracerId",
                    }
                )?, lc_clock),
            }
        } else {
            return Err(ReadError::InvalidContent {
                session_id, segment_id, segment_index,
                message: "Either event_id must be present, or both lc_tracer_id and lc_clock must both be present",
            });
        };

        Ok(model::LogEntry {
            session_id,
            segment_id,
            segment_index,
            tracer_id: l
                .tracer_id
                .try_into()
                .map_err(|_e| ReadError::InvalidContent {
                    session_id,
                    segment_id,
                    segment_index,
                    message: "When lc_tracer_id is present, it must be a valid ekotrac::TracerId",
                })?,
            data,
            receive_time: l.receive_time,
        })
    }
}

pub fn write_csv_log_entries<'a, W: Write, E: IntoIterator<Item = &'a model::LogEntry>>(
    w: &mut W,
    entries: E,
    include_header_row: bool,
) -> Result<(), csv::Error> {
    let mut csv = csv::WriterBuilder::new()
        .has_headers(include_header_row)
        .from_writer(w);

    for e in entries.into_iter() {
        let line: LogFileLine = e.into();
        csv.serialize(line)?;
    }

    csv.flush()?;
    Ok(())
}

#[derive(Debug)]
pub enum ReadError {
    InvalidContent {
        session_id: model::SessionId,
        segment_id: model::SegmentId,
        segment_index: u32,
        message: &'static str,
    },
    Csv(csv::Error),
}

impl From<csv::Error> for ReadError {
    fn from(e: csv::Error) -> ReadError {
        ReadError::Csv(e)
    }
}

pub fn read_csv_log_entries<R: Read>(r: &mut R) -> Result<Vec<model::LogEntry>, ReadError> {
    let mut csv = csv::Reader::from_reader(r);
    csv.deserialize()
        .map(|line| Ok(model::LogEntry::try_from(&line?)?))
        .collect()
}

/// Just the segment information needed for indexing
#[derive(Clone, Debug)]
struct SegmentMetadata {
    id: model::SegmentId,
    tracer_id: ekotrace::TracerId,
    logical_clock: HashMap<ekotrace::TracerId, u32>,
}

impl SegmentMetadata {
    fn local_clock(&self) -> Option<u32> {
        match self.logical_clock.get(&self.tracer_id) {
            Some(c) => Some(*c),
            None => None,
        }
    }
}

#[derive(Debug)]
struct SegmentMetadataIndex(HashMap<model::SegmentId, SegmentMetadata>);
impl SegmentMetadataIndex {
    fn new() -> SegmentMetadataIndex {
        SegmentMetadataIndex(HashMap::new())
    }

    fn insert(&mut self, smd: SegmentMetadata) {
        self.0.insert(smd.id, smd);
    }
}

// source tracer id -> local clock value -> segment id
#[derive(Debug)]
struct LCIndex(HashMap<ekotrace::TracerId, BTreeMap<u32, model::SegmentId>>);

#[derive(Debug)]
pub enum LCIndexError {
    SegmentMissingOwnClock,
}

impl LCIndex {
    fn new() -> LCIndex {
        LCIndex(HashMap::new())
    }

    fn add(&mut self, smd: &SegmentMetadata) {
        // This should always be true
        if let Some(local_clock) = smd.local_clock() {
            self.0
                .entry(smd.tracer_id)
                .or_insert_with(BTreeMap::new)
                .insert(local_clock, smd.id);
        }
    }

    fn find_segment_direct_ancestors(
        &self,
        smd: &SegmentMetadata,
        smd_index: &SegmentMetadataIndex,
    ) -> Result<HashSet<model::SegmentId>, LCIndexError> {
        let mut segs = HashSet::new();
        let local_clock = *smd.logical_clock.get(&smd.tracer_id).unwrap();

        let mut local_ancestors = vec![];
        self.0
            .get(&smd.tracer_id)
            .unwrap()
            .range(local_clock.saturating_sub(5)..local_clock)
            .rfold((), |_, (_, &sid)| {
                local_ancestors.push(smd_index.0.get(&sid).unwrap())
            });

        // Then, go through all the other (non-local) clock entries.
        'other_clock_entry_loop: for (bucket_tracer_id, bucket_clock) in smd.logical_clock.iter() {
            if *bucket_tracer_id != smd.tracer_id {
                // check if any direct ancestor (segs from the same source
                // tracer) already has this same exact clock entry; if so, skip
                // making an edge for this one, since it would be redundant.

                for local_ancestor in local_ancestors.iter() {
                    if local_ancestor.logical_clock.get(&bucket_tracer_id) == Some(&bucket_clock) {
                        continue 'other_clock_entry_loop;
                    }
                }
            }

            if let Some((_, sid)) = self
                .0
                .get(&bucket_tracer_id)
                .ok_or(LCIndexError::SegmentMissingOwnClock)?
                .range(0..*bucket_clock)
                .last()
            {
                segs.insert(*sid);
            }
        }

        Ok(segs)
    }
}

pub fn synthesize_cross_segment_links<'a, L: IntoIterator<Item = &'a model::LogEntry>>(
    log: L,
    session_id: model::SessionId,
) -> Result<Vec<model::CrossSegmentLink>, LCIndexError> {
    // build indexes
    let mut smi = SegmentMetadataIndex::new();
    for (segment_id, clock_events) in &log
        .into_iter()
        .filter(|e| e.session_id == session_id && e.is_clock())
        .group_by(|e| e.segment_id)
    {
        let mut logical_clock = HashMap::new();
        let mut tracer_id = None;
        for e in clock_events {
            // this should be the case every time, because of the filter above
            if let model::LogEntryData::LogicalClock(bucket_id, count) = e.data {
                logical_clock.insert(bucket_id, count);
                tracer_id = Some(e.tracer_id);
            }
        }

        smi.insert(SegmentMetadata {
            id: segment_id,
            // since you can't have made a group with nothing in it, we're
            // guaranteed to always get a Some() here.
            tracer_id: tracer_id.unwrap(),
            logical_clock,
        });
    }

    let mut lci = LCIndex::new();
    for (_, smd) in smi.0.iter() {
        lci.add(&smd);
    }

    let mut links = vec![];
    for (_, smd) in smi.0.iter() {
        for ancestor in lci.find_segment_direct_ancestors(&smd, &smi)?.into_iter() {
            links.push(model::CrossSegmentLink {
                session_id,
                before: ancestor,
                after: smd.id,
            })
        }
    }

    Ok(links)
}

pub struct SegmentGraphNode {
    pub tracer_id: ekotrace::TracerId,
    pub segment_id: model::SegmentId,
    pub event_count: usize,
}

pub fn build_segment_graph<'a, L: IntoIterator<Item = &'a model::LogEntry> + Copy>(
    log: L,
    session_id: model::SessionId,
) -> Result<Graph<SegmentGraphNode, ()>, LCIndexError> {
    let mut seg_graph = Graph::new();
    let mut node_index_for_segment = HashMap::new();

    for ((tracer_id, segment_id), events) in &log
        .into_iter()
        .filter(|e| e.session_id == session_id)
        .group_by(|e| (e.tracer_id, e.segment_id))
    {
        let node_index = seg_graph.add_node(SegmentGraphNode {
            tracer_id,
            segment_id,
            event_count: events.count(),
        });
        node_index_for_segment.insert(segment_id, node_index);
    }

    for l in synthesize_cross_segment_links(log, session_id)?.iter() {
        // these are 'backwards', because we want the graph arrows to point to what comes before.
        seg_graph.update_edge(
            *node_index_for_segment.get(&l.after).unwrap(),
            *node_index_for_segment.get(&l.before).unwrap(),
            (),
        );
    }

    Ok(seg_graph)
}

pub fn build_log_entry_graph<'a, L: IntoIterator<Item = &'a model::LogEntry> + Copy>(
    log: L,
    session_id: model::SessionId,
) -> Result<Graph<model::LogEntry, ()>, LCIndexError> {
    let mut log_entry_graph = Graph::new();
    let mut first_node_index_in_segment = HashMap::new();
    let mut last_node_index_in_segment = HashMap::new();

    for log_entry in log.into_iter() {
        let segment_id = log_entry.segment_id;
        let node_index = log_entry_graph.add_node((*log_entry).clone());

        // within a segment, events come in order. Hook them up in the graph.
        if let Some(last_node_index) = last_node_index_in_segment.get(&segment_id) {
            log_entry_graph.update_edge(node_index, *last_node_index, ());
        }

        first_node_index_in_segment
            .entry(segment_id)
            .or_insert(node_index);

        last_node_index_in_segment.insert(segment_id, node_index);
    }

    for l in synthesize_cross_segment_links(log, session_id)?.iter() {
        // these are 'backwards', because we want the graph arrows to point to
        // what comes before.
        log_entry_graph.update_edge(
            first_node_index_in_segment[&l.after],
            last_node_index_in_segment[&l.before],
            (),
        );
    }

    Ok(log_entry_graph)
}

#[cfg(test)]
mod test {
    use super::*;
    use ekotrace::EventId;
    use proptest::prelude::*;

    prop_compose! {
        pub(crate) fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
            raw_id
        }
    }

    fn arb_log_file_line() -> impl Strategy<Value = LogFileLine> {
        (
            any::<u32>(),
            any::<u32>(),
            any::<u32>(),
            model::test::arb_datetime(),
            any::<u32>(),
            // util::model::EventId requires a valid event id now.
            proptest::option::of(gen_raw_user_event_id()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
            proptest::option::of(any::<u32>()),
        )
            .prop_map(
                |(
                    session_id,
                    segment_id,
                    segment_index,
                    receive_time,
                    tracer_id,
                    event_id,
                    event_payload,
                    lc_tracer_id,
                    lc_clock,
                )| LogFileLine {
                    session_id,
                    segment_id,
                    segment_index,
                    receive_time,
                    tracer_id,
                    event_id,
                    // The event payload can only be set if there's also
                    // an event id.
                    event_payload: if event_id.is_some() && event_payload.is_some() {
                        event_payload
                    } else {
                        None
                    },
                    lc_tracer_id,
                    lc_clock,
                },
            )
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 1000, .. ProptestConfig::default()})]

        #[test]
        fn entry_to_line_round_trip(entry in model::test::arb_log_entry())
        {
            let line : LogFileLine = (&entry).into();
            match model::LogEntry::try_from(&line) {
                Err(err) => prop_assert!(false, "convert back error: {:?}", err),
                Ok(e2) => prop_assert_eq!(entry, e2),
            }
        }


        #[test]
        fn line_to_entry_round_trip(line in arb_log_file_line())
        {
            match model::LogEntry::try_from(&line) {
                // This should fail sometimes, but always in the same way
                Err(ReadError::InvalidContent{
                    session_id,
                    segment_id,
                    segment_index,
                    .. }) =>
                {
                    prop_assert_eq!(session_id, line.session_id.into());
                    prop_assert_eq!(segment_id, line.segment_id.into());
                    prop_assert_eq!(segment_index, u32::from(line.segment_index));
                }

                Err(err) =>
                    prop_assert!(false, "Unexpected conversion error: {:?}", err),

                Ok(entry) => {
                    let l2: LogFileLine = (&entry).into();
                    prop_assert_eq!(line, l2);
                },
            }
        }

        #[test]
        fn round_trip_serialization(
            entries in proptest::collection::vec(model::test::arb_log_entry(),
                                                 0..15))
        {
            let mut data = Vec::<u8>::new();
            prop_assert!(write_csv_log_entries(&mut data, &entries, true).is_ok());

            let read_back = read_csv_log_entries(&mut data.as_slice());

            match read_back {
                Err(e) => prop_assert!(false, "read_back error: {:?}", e),
                Ok(es) => prop_assert_eq!(entries, es),
            }
        }
    }
}
