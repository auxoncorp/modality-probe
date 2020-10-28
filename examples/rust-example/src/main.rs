use crossbeam::{crossbeam_channel, thread};
use log::{info, trace};
use modality_probe::{
    expect, initialize_at, record, record_w_i8, CausalSnapshot, ModalityProbe, Probe,
    RestartCounterProvider,
};
use rand::{thread_rng, Rng};
use std::{env, fmt, net::UdpSocket};

// Import the generated component manifest definitions
mod component_definitions;
use component_definitions::*;

const PROBE_SIZE: usize = 1024;
const REPORT_SIZE: usize = 1024;
const COLLECTOR_ADDR: &str = "127.0.0.1:2718";

fn main() {
    // Default to info level if not set
    if env::var("RUST_LOG").is_err() {
        env::set_var("RUST_LOG", "info");
    }
    env_logger::init();

    info!("Modality probe reports will be sent to {}", COLLECTOR_ADDR);

    let (tx, rx) = crossbeam_channel::unbounded();

    thread::scope(|s| {
        let a = s.spawn(move |_| {
            measurement_producer_thread(tx);
        });

        let b = s.spawn(move |_| {
            measurement_consumer_thread(rx);
        });

        let res = a.join();
        assert!(res.is_ok());

        let res = b.join();
        assert!(res.is_ok());
    })
    .unwrap();

    info!("All done");
}

#[derive(Debug)]
pub struct Measurement {
    pub m: i8,
    pub snapshot: CausalSnapshot,
}

impl fmt::Display for Measurement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.m)
    }
}

fn measurement_producer_thread(tx: crossbeam_channel::Sender<Measurement>) {
    info!("Sensor measurement producer thread starting");

    let mut storage = [std::mem::MaybeUninit::new(0u8); PROBE_SIZE];
    let probe = initialize_at!(
        &mut storage,
        PRODUCER_PROBE,
        RestartCounterProvider::NoRestartTracking,
        tags!("rust-example", "measurement", "producer"),
        "Measurement producer probe"
    )
    .expect("Could not initialize ModalityProbe");

    let mut report_buffer = vec![0u8; REPORT_SIZE];
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");

    record!(
        probe,
        PRODUCER_STARTED,
        "Measurement producer thread started",
        tags!("producer")
    );

    let instant = probe.now();
    trace!("Producer now {:?}", instant);

    let mut rng = thread_rng();
    let m: i8 = 1 + rng.gen_range(-1, 2);

    record_w_i8!(
        probe,
        PRODUCER_MEASUREMENT_SAMPLED,
        m,
        tags!("producer", "measurement sample"),
        "Measurement producer sampled a value for transmission"
    );

    // Construct a measurement for transmission with a Modality probe snapshot in-band
    let snapshot = probe.produce_snapshot();
    let measurement = Measurement { m, snapshot };

    let tx_status = tx.send(measurement);
    expect!(
        probe,
        PRODUCER_MEASUREMENT_SENT,
        tx_status.is_ok(),
        "Measurement producer sent a measurement",
        tags!("producer", "transmit", "SEVERITY_10")
    );

    record!(
        probe,
        PRODUCER_SHUTDOWN,
        "Measurement producer thread shutting down",
        tags!("producer")
    );

    send_report(&socket, probe, &mut report_buffer);
}

fn measurement_consumer_thread(rx: crossbeam_channel::Receiver<Measurement>) {
    info!("Sensor measurement consumer thread starting");

    let mut storage = [std::mem::MaybeUninit::new(0u8); PROBE_SIZE];
    let probe = initialize_at!(
        &mut storage,
        CONSUMER_PROBE,
        RestartCounterProvider::NoRestartTracking,
        tags!("rust-example", "measurement", "consumer"),
        "Measurement consumer probe"
    )
    .expect("Could not initialize ModalityProbe");

    let mut report_buffer = vec![0u8; REPORT_SIZE];
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");

    record!(
        probe,
        CONSUMER_STARTED,
        "Measurement consumer thread started",
        tags!("consumer")
    );

    // Wait for a new measurement from the producer or a disconnect
    if let Ok(measurement) = rx.recv() {
        let instant = probe.now();
        trace!("Consumer now {:?}", instant);

        // Merge the snapshot from the producer's probe with our (the consumer) probe
        probe
            .merge_snapshot(&measurement.snapshot)
            .expect("Could not merge snapshot");

        record_w_i8!(
            probe,
            CONSUMER_MEASUREMENT_RECVD,
            measurement.m,
            tags!("consumer", "measurement"),
            "Measurement consumer recvd a new value"
        );

        info!("Consumer recvd {}", measurement);
    }

    record!(
        probe,
        CONSUMER_SHUTDOWN,
        "Measurement consumer thread shutting down",
        tags!("producer")
    );

    send_report(&socket, probe, &mut report_buffer);
}

/// Helper function to send a probe report to a collector at `COLLECTOR_ADDR`
fn send_report<'a>(socket: &UdpSocket, probe: &mut ModalityProbe<'a>, report_buffer: &mut [u8]) {
    let n_report_bytes = probe
        .report(report_buffer)
        .expect("Could not produce a report");
    if let Some(nonzero_report_size) = n_report_bytes {
        socket
            .send_to(&report_buffer[..nonzero_report_size.get()], COLLECTOR_ADDR)
            .expect("Could not send_to");
    }
}
