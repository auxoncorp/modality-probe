//! Basic Ekotrace event recording and reporting example.
//!
//! Before building this example, run:
//!
//! ```
//! ekotrace manifest-gen --events-csv-file events.csv --tracers-csv-file tracers.csv ./
//!
//! ekotrace header-gen --lang Rust events.csv tracers.csv > tracing_ids/mod.rs
//! ```

// The generated event and tracer identifiers
mod tracing_ids;

use crate::tracing_ids::*;
use ekotrace::{
    try_expect, try_initialize_at, try_record, try_record_w_u32, BulkReporter, Ekotrace,
};
use std::net::UdpSocket;
use std::{thread, time};

fn main() {
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");
    let remote = "127.0.0.1:2718";

    let mut storage = [0u8; 1024];
    let tracer = try_initialize_at!(
        &mut storage,
        LOCATION_ID_FOO,
        "tags=example",
        "Example location"
    )
    .expect("Could not initialize Ekotrace");

    let mut loop_counter = 0;
    loop {
        try_record!(
            tracer,
            TOP_OF_THE_LOOP,
            "At the top of the loop",
            "tags=example;my-tag"
        )
        .expect("Could not record event");

        try_expect!(
            tracer,
            MOD10_CONDITION_EVENT,
            loop_counter % 10 == 0,
            "Loop counter % 10 event",
            "tags=example"
        )
        .expect("Could not record event");

        if loop_counter % 2 == 0 {
            try_record!(tracer, LOOP_COUNTER_EVENT, "Loop counter event happened")
                .expect("Could not record event");
        }

        // Send a report the collector every four iterations
        if loop_counter % 4 == 0 {
            println!("Sending report to {}", remote);
            let mut report_buffer = [0u8; 1024];
            let n_report_bytes = tracer
                .report(&mut report_buffer)
                .expect("Could not produce a report");
            socket
                .send_to(&report_buffer[..n_report_bytes], remote)
                .expect("Could not send_to");
            try_record_w_u32!(
                tracer,
                REPORT_CREATED,
                n_report_bytes as u32,
                "tags=another tag",
                "Report created"
            )
            .expect("could not record event with metadata");
        }

        loop_counter += 1;

        thread::sleep(time::Duration::from_millis(250));
    }
}
