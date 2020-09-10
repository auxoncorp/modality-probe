use crossbeam::{crossbeam_channel, thread};
use log::{info, trace};
use modality_probe::{
    try_expect, try_initialize_at, try_record, try_record_w_i8, CausalSnapshot, ModalityProbe,
    Probe, RestartCounterProvider,
};
use rand::{thread_rng, Rng};
use std::{
    env, fmt,
    net::UdpSocket,
    process,
    sync::atomic::{AtomicUsize, Ordering},
    sync::Arc,
    thread::sleep,
    time::Duration,
};

// Import the generated component manifest definitions
mod component_definitions;
use component_definitions::*;

const PROBE_SIZE: usize = 1024;
const REPORT_SIZE: usize = 1024;
const COLLECTOR_ADDR: &str = "127.0.0.1:2718";
const SLEEP_DURATION: Duration = Duration::from_millis(100);

fn main() {
    // Default to info level if not set
    if env::var("RUST_LOG").is_err() {
        env::set_var("RUST_LOG", "info");
    }
    env_logger::init();
    let running = Arc::new(AtomicUsize::new(0));
    let r_producer = running.clone();
    let r_consumer = running.clone();
    let r = running;
    ctrlc::set_handler(move || {
        let prev = r.fetch_add(1, Ordering::SeqCst);
        if prev == 0 {
            info!("Shutting down");
        } else {
            info!("Force exit");
            process::exit(0);
        }
    })
    .expect("Error setting Ctrl-C handler");

    info!("Modality probe reports will be sent to {}", COLLECTOR_ADDR);

    let (tx, rx) = crossbeam_channel::unbounded();

    thread::scope(|s| {
        let a = s.spawn(move |_| {
            measurement_producer_thread(r_producer, tx);
        });

        let b = s.spawn(move |_| {
            measurement_consumer_thread(r_consumer, rx);
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

fn measurement_producer_thread(
    running: Arc<AtomicUsize>,
    tx: crossbeam_channel::Sender<Measurement>,
) {
    info!("Sensor measurement producer thread starting");

    let mut storage = [0u8; PROBE_SIZE];
    let probe = try_initialize_at!(
        &mut storage,
        PRODUCER_PROBE,
        RestartCounterProvider::NoRestartTracking,
        tags!("rust-example", "measurement", "producer"),
        "Measurement producer probe"
    )
    .expect("Could not initialize ModalityProbe");

    let mut report_buffer = vec![0u8; REPORT_SIZE];
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");

    // Producer will send a randomly moving i8 measurement
    let mut rng = thread_rng();
    let mut m: i8 = 1;

    try_record!(
        probe,
        PRODUCER_STARTED,
        "Measurement producer thread started",
        tags!("producer")
    )
    .expect("Could not record event");

    send_report(&socket, probe, &mut report_buffer);

    let mut loop_counter: usize = 0;
    while running.load(Ordering::SeqCst) == 0 {
        let instant = probe.now();
        trace!("Producer top of the loop {:?}", instant);

        let delta: i8 = rng.gen_range(-1, 2);
        m = m.wrapping_add(delta);

        try_record_w_i8!(
            probe,
            PRODUCER_MEASUREMENT_SAMPLED,
            m,
            tags!("producer", "measurement sample"),
            "Measurement producer sampled a value for transmission"
        )
        .expect("could not record event with payload");

        // Construct a measurement for transmission with a Modality probe snapshot in-band
        let snapshot = probe.produce_snapshot();
        let measurement = Measurement { m, snapshot };

        let tx_status = tx.send(measurement);
        try_expect!(
            probe,
            PRODUCER_TX_STATUS_OK,
            tx_status.is_ok(),
            "Measurement producer send result status",
            tags!("producer", "SEVERITY_10")
        )
        .expect("Could not record event");

        if tx_status.is_err() {
            info!("Producer failed to send measurement");
            break;
        }

        // Send a report periodically, every 10 iterations here ~= once a second
        loop_counter = loop_counter.wrapping_add(1);
        if loop_counter % 10 == 0 {
            send_report(&socket, probe, &mut report_buffer);
        }

        sleep(SLEEP_DURATION);
    }

    try_record!(
        probe,
        PRODUCER_SHUTDOWN,
        "Measurement producer thread shutting down",
        tags!("producer")
    )
    .expect("Could not record event");

    send_report(&socket, probe, &mut report_buffer);
}

fn measurement_consumer_thread(
    running: Arc<AtomicUsize>,
    rx: crossbeam_channel::Receiver<Measurement>,
) {
    info!("Sensor measurement consumer thread starting");

    let mut storage = [0u8; PROBE_SIZE];
    let probe = try_initialize_at!(
        &mut storage,
        CONSUMER_PROBE,
        RestartCounterProvider::NoRestartTracking,
        tags!("rust-example", "measurement", "consumer"),
        "Measurement consumer probe"
    )
    .expect("Could not initialize ModalityProbe");

    let mut report_buffer = vec![0u8; REPORT_SIZE];
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Could not bind");

    try_record!(
        probe,
        CONSUMER_STARTED,
        "Measurement consumer thread started",
        tags!("consumer")
    )
    .expect("Could not record event");

    send_report(&socket, probe, &mut report_buffer);

    let mut loop_counter: usize = 0;
    while running.load(Ordering::SeqCst) == 0 {
        // Wait for a new measurement from the producer or a disconnect
        let measurement = if let Ok(m) = rx.recv() {
            m
        } else {
            break;
        };

        let instant = probe.now();
        trace!("Consumer top of the loop {:?}", instant);

        // Merge the snapshot from the producer's probe with our (the consumer) probe
        probe
            .merge_snapshot(&measurement.snapshot)
            .expect("Could not merge snapshot");

        try_record_w_i8!(
            probe,
            CONSUMER_MEASUREMENT_RECVD,
            measurement.m,
            tags!("consumer", "measurement"),
            "Measurement consumer recvd a new value"
        )
        .expect("could not record event with payload");

        info!("Consumer recvd {}", measurement);

        // Send a report periodically, every 10 iterations here ~= once a second
        loop_counter = loop_counter.wrapping_add(1);
        if loop_counter % 10 == 0 {
            send_report(&socket, probe, &mut report_buffer);
        }
    }

    try_record!(
        probe,
        CONSUMER_SHUTDOWN,
        "Measurement consumer thread shutting down",
        tags!("producer")
    )
    .expect("Could not record event");

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
