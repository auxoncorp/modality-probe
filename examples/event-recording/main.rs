//! Basic Ekotrace event recording and reporting example.
//!
//! Before building this example, run:
//!
//! ```
//! ekotrace-manifest-gen --events-csv-file events.csv --tracers-csv-file tracers.csv ./
//!
//! ekotrace-header-gen --lang Rust events.csv tracers.csv > tracing_ids.rs
//! ```

use crate::tracing_ids::*;
use ekotrace::{Ekotrace, Tracer};
use std::net::UdpSocket;
use std::{thread, time};

// The generated event and tracer identifiers
mod tracing_ids;

fn main() {
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");
    let remote = "127.0.0.1:2718";

    let mut storage = [0u8; 1024];
    let tracer = Ekotrace::try_initialize_at(&mut storage, LOCATION_ID_FOO)
        .expect("Could not initialize Ekotrace");

    let mut loop_counter = 0;
    loop {
        tracer
            .try_record_event(TOP_OF_THE_LOOP)
            .expect("Could not record event");

        if loop_counter % 2 == 0 {
            tracer
                .try_record_event(LOOP_COUNTER_EVEN)
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
        }

        loop_counter += 1;

        thread::sleep(time::Duration::from_millis(250));
    }
}
