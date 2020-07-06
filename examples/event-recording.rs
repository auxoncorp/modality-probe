//! Basic ModalityProbe event recording and reporting example.
//!
//! Before building this example, run:
//!
//! ```
//! modality-probe manifest-gen --output-path . ./
//!
//! modality-probe header-gen --lang Rust --probes example-component/probes.csv --events example-component/events.csv --output-path generated_ids/mod.rs
//! ```

// The generated identifiers
mod generated_ids;

use crate::generated_ids::*;
use modality_probe::{
    try_expect, try_initialize_at, try_record, try_record_w_u32, BulkReporter, ModalityProbe,
};
use std::net::UdpSocket;
use std::{thread, time};

fn main() {
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");
    let remote = "127.0.0.1:2718";

    let mut storage = [0u8; 1024];
    let probe = try_initialize_at!(
        &mut storage,
        PROBE_ID_FOO,
        EXAMPLE_COMPONENT,
        tags!("example"),
        "Example probe"
    )
    .expect("Could not initialize ModalityProbe");

    let mut loop_counter = 0;
    loop {
        try_record!(
            probe,
            TOP_OF_THE_LOOP,
            "At the top of the loop",
            tags!("example", "my-tag")
        )
        .expect("Could not record event");

        try_expect!(
            probe,
            MOD10_CONDITION_EVENT,
            loop_counter % 10 == 0,
            "Loop counter % 10 event",
            tags!("example")
        )
        .expect("Could not record event");

        if loop_counter % 2 == 0 {
            try_record!(probe, LOOP_COUNTER_EVENT, "Loop counter event happened")
                .expect("Could not record event");
        }

        // Send a report the collector every four iterations
        if loop_counter % 4 == 0 {
            println!("Sending report to {}", remote);
            let mut report_buffer = [0u8; 1024];
            let n_report_bytes = probe
                .report(&mut report_buffer)
                .expect("Could not produce a report");
            socket
                .send_to(&report_buffer[..n_report_bytes], remote)
                .expect("Could not send_to");
            try_record_w_u32!(
                probe,
                REPORT_CREATED,
                n_report_bytes as u32,
                tags!("another tag"),
                "Report created"
            )
            .expect("could not record event with metadata");
        }

        loop_counter += 1;

        thread::sleep(time::Duration::from_millis(250));
    }
}
