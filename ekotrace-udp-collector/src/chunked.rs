use chrono::{DateTime, Utc};
use std::collections::{BTreeMap, HashMap};
use util::alloc_log_report::LogReport;

pub struct ChunkHandlingConfig {
    pub max_total_open_time: chrono::Duration,
    pub max_time_since_last_chunk: chrono::Duration,
}

impl Default for ChunkHandlingConfig {
    fn default() -> Self {
        ChunkHandlingConfig {
            max_total_open_time: chrono::Duration::seconds(600),
            max_time_since_last_chunk: chrono::Duration::seconds(120),
        }
    }
}

pub struct ChunkHandler {
    config: ChunkHandlingConfig,

    #[allow(clippy::type_complexity)]
    open_reports: HashMap<
        (ekotrace::TracerId, u16),
        BTreeMap<u16, (ekotrace::report::chunked::NativeChunk, DateTime<Utc>)>,
    >,
}

impl ChunkHandler {
    pub fn new(config: ChunkHandlingConfig) -> Self {
        ChunkHandler {
            config,
            open_reports: Default::default(),
        }
    }

    pub fn add_incoming_chunk(&mut self, message_bytes: &[u8], receive_time: DateTime<Utc>) {
        use ekotrace::report::chunked::*;
        let native_chunk = match NativeChunk::from_wire_bytes(message_bytes) {
            Ok(nc) => nc,
            Err(e) => {
                eprintln!(
                    "Could not interpret a report chunk into native representation: {:?}",
                    e
                );
                return;
            }
        };
        let key = (
            native_chunk.header().location_id,
            native_chunk.header().chunk_group_id,
        );
        let entry = self.open_reports.entry(key).or_insert_with(BTreeMap::new);
        if let Some((extant_chunk, _prior_recv_time)) =
            entry.get(&native_chunk.header().chunk_index)
        {
            // Collision! Unless this chunk amazingly has the exact same content as the prior entry
            // and can be ignored as a duplicate, we should assume that the node is churning out reports
            // quickly and looping through the report id space (a u16) fast, meaning the most likely
            // situation is that the old chunks are stale and should be discarded.
            if extant_chunk != &native_chunk {
                entry.clear();
                entry.insert(
                    native_chunk.header().chunk_index,
                    (native_chunk, receive_time),
                );
            } else {
                eprintln!("Ignoring duplicate chunk: Location Tracer Id: {:?}, Report Group Id: {:?}, Chunk Index: {:?}",
                          native_chunk.header().location_id, native_chunk.header().chunk_group_id, native_chunk.header().chunk_index);
            }
        } else {
            entry.insert(
                native_chunk.header().chunk_index,
                (native_chunk, receive_time),
            );
        }
    }

    pub fn materialize_completed_reports(&mut self) -> Vec<(LogReport, DateTime<Utc>)> {
        let mut completed_report_keys = Vec::new();
        for ((tracer_id, report_group_id), chunks) in self.open_reports.iter() {
            let mut prior_chunk_index = None;
            for (chunk_index, (chunk, _received_at)) in chunks.iter() {
                if let Some(prior_chunk_index) = prior_chunk_index {
                    if *chunk_index != prior_chunk_index + 1 {
                        break;
                    }
                    if chunk.header().is_last_chunk {
                        completed_report_keys.push((*tracer_id, *report_group_id));
                        break;
                    }
                } else if *chunk_index != 0 {
                    break;
                } else if chunk.header().is_last_chunk {
                    completed_report_keys.push((*tracer_id, *report_group_id));
                    break;
                } else {
                    prior_chunk_index = Some(*chunk_index)
                }
            }
        }
        let mut complete_reports = Vec::new();
        for key in completed_report_keys {
            // We just found these keys by iterating through the map earlier, we can
            // feel confident that they're still there and unwrap.
            let chunks = self.open_reports.remove(&key).unwrap();
            let mut log_payload_items = Vec::new();
            let mut latest_receive_time = None;
            for (_k, (chunk, recv_time)) in chunks.into_iter() {
                if let ekotrace::report::chunked::NativeChunk::Log { contents, .. } = chunk {
                    log_payload_items.extend_from_slice(contents.log_slice());
                    if let Some(prior_recv_time) = latest_receive_time {
                        if prior_recv_time < recv_time {
                            latest_receive_time = Some(recv_time);
                        }
                    } else {
                        latest_receive_time = Some(recv_time);
                    }
                } else {
                    break;
                }
            }
            // N.B. - If we decide we want to log extension bytes, will need to pipe them through here
            match LogReport::try_from_log(key.0, &log_payload_items, &[]) {
                Ok(report) => {
                    complete_reports.push((report, latest_receive_time.unwrap_or_else(Utc::now)));
                }
                Err(e) => {
                    eprintln!("Error attempting to materialize a complete report: {:?}", e);
                    // No further clean-up action required because the offending report chunks
                    // have already been removed from the state, above.
                }
            }
        }
        complete_reports
    }

    pub fn remove_stale_reports(&mut self) {
        let now = Utc::now();
        let mut keys_to_remove = Vec::new();
        for (k, v) in &self.open_reports {
            let mut earliest_received = None;
            let mut second_latest_received = None;
            let mut latest_received = None;
            for (_chunk, recv_time) in v.values() {
                if let Some(earliest) = earliest_received {
                    if recv_time < earliest {
                        earliest_received = Some(recv_time);
                    }
                } else {
                    earliest_received = Some(recv_time);
                }
                if let Some(latest) = latest_received {
                    if recv_time > latest {
                        latest_received = Some(recv_time);
                        second_latest_received = Some(latest);
                    }
                } else {
                    latest_received = Some(recv_time);
                    second_latest_received = Some(recv_time);
                }
            }
            if let (Some(earliest), Some(latest)) = (earliest_received, latest_received) {
                if *latest - *earliest >= self.config.max_total_open_time {
                    keys_to_remove.push(*k);
                    continue;
                }
            }
            if let Some(earliest) = earliest_received {
                if now - *earliest >= self.config.max_total_open_time {
                    keys_to_remove.push(*k);
                    continue;
                }
            }
            if let (Some(second_latest), Some(latest)) = (second_latest_received, latest_received) {
                if *latest - *second_latest >= self.config.max_time_since_last_chunk {
                    keys_to_remove.push(*k);
                    continue;
                }
            }
        }
        for k in keys_to_remove {
            self.open_reports.remove(&k);
        }
    }
}

pub fn matches_chunk_fingerprint(message_bytes: &[u8]) -> bool {
    if message_bytes.len() >= std::mem::size_of::<ekotrace::report::chunked::WireChunkHeader>() {
        [
            message_bytes[0],
            message_bytes[1],
            message_bytes[2],
            message_bytes[3],
        ] == ekotrace::report::chunked::chunk_framing_fingerprint()
    } else {
        false
    }
}
