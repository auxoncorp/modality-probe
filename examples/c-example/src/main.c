#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <syslog.h>
#include <assert.h>

#include "probe.h"

/* Generated component manifest definitions */
#include "component_definitions.h"

#define PROBE_SIZE (1024)
#define REPORT_SIZE (1024)
#define COLLECTOR_ADDRESS "127.0.0.1"
#define COLLECTOR_PORT (2718)

typedef struct
{
    int8_t m;
    modality_probe_causal_snapshot snapshot;
} measurement_s;

static struct sockaddr_in g_collector_addr;
static int g_report_socket = -1;
static uint8_t g_report_buffer[REPORT_SIZE];

static modality_probe *g_producer_probe = MODALITY_PROBE_NULL_INITIALIZER;
static uint8_t g_producer_probe_buffer[PROBE_SIZE];
static measurement_s g_producer_measurement;

static modality_probe *g_consumer_probe = MODALITY_PROBE_NULL_INITIALIZER;
static uint8_t g_consumer_probe_buffer[PROBE_SIZE];

/* Simple 1-element deep pretend queue */
static measurement_s *g_measurement_queue = NULL;

static void send_report(modality_probe * const probe)
{
    size_t report_size;
    const size_t err = modality_probe_report(
            probe,
            &g_report_buffer[0],
            sizeof(g_report_buffer),
            &report_size);
    assert(err == MODALITY_PROBE_ERROR_OK);

    if(report_size != 0)
    {
        const ssize_t status = sendto(
                g_report_socket,
                &g_report_buffer[0],
                report_size,
                0,
                (const struct sockaddr*) &g_collector_addr,
                sizeof(g_collector_addr));
        assert(status != -1);
    }
}

static void init_producer(void)
{
    size_t err;

    printf("Sensor measurement producer starting\n");

    (void) memset(&g_producer_measurement, 0, sizeof(g_producer_measurement));

    err = MODALITY_PROBE_INIT(
            &g_producer_probe_buffer[0],
            sizeof(g_producer_probe_buffer),
            PRODUCER_PROBE,
            NULL,
            NULL,
            &g_producer_probe,
            MODALITY_TAGS("c-example", "measurement", "producer"),
            "Measurement producer probe");
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD(
            g_producer_probe,
            PRODUCER_STARTED,
            MODALITY_TAGS("producer"),
            "Measurement producer started");
    assert(err == MODALITY_PROBE_ERROR_OK);
}

static void deinit_producer(void)
{
    size_t err;

    err = MODALITY_PROBE_RECORD(
            g_producer_probe,
            PRODUCER_SHUTDOWN,
            MODALITY_TAGS("producer"),
            "Measurement producer shutting down");
    assert(err == MODALITY_PROBE_ERROR_OK);

    send_report(g_producer_probe);
}

static void run_producer(void)
{
    size_t err;

    const modality_probe_instant now = modality_probe_now(g_producer_probe);
    syslog(
            LOG_INFO,
            "Producer now "
            "(id: %" PRIu32 ", epoch: %" PRIu16 ", ticks: %" PRIu16 ", event_count: %" PRIu32 ")\n",
            now.clock.id,
            now.clock.epoch,
            now.clock.ticks,
            now.event_count);

    const int8_t sample = g_producer_measurement.m + (int8_t) (-1 + (rand() % 4));

    err = MODALITY_PROBE_RECORD_W_I8(
            g_producer_probe,
            PRODUCER_MEASUREMENT_SAMPLED,
            sample,
            MODALITY_TAGS("producer", "measurement sample"),
            "Measurement producer sampled a value for transmission");
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = modality_probe_produce_snapshot(
            g_producer_probe,
            &g_producer_measurement.snapshot);
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_EXPECT(
            g_producer_probe,
            PRODUCER_SAMPLE_DELTA_OK,
            (sample - g_producer_measurement.m) <= 2,
            MODALITY_TAGS("producer", "SEVERITY_10"),
            "Measurement delta within ok range");
    assert(err == MODALITY_PROBE_ERROR_OK);

    g_producer_measurement.m = sample;
    g_measurement_queue = &g_producer_measurement;

    err = MODALITY_PROBE_RECORD(
            g_producer_probe,
            PRODUCER_MEASUREMENT_SENT,
            MODALITY_TAGS("producer", "transmit"),
            "Measurement producer sent a measurement");
    assert(err == MODALITY_PROBE_ERROR_OK);
}

static void init_consumer(void)
{
    size_t err;

    printf("Sensor measurement consumer starting\n");

    err = MODALITY_PROBE_INIT(
            &g_consumer_probe_buffer[0],
            sizeof(g_consumer_probe_buffer),
            CONSUMER_PROBE,
            NULL,
            NULL,
            &g_consumer_probe,
            MODALITY_TAGS("c-example", "measurement", "consumer"),
            "Measurement consumer probe");
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD(
            g_consumer_probe,
            CONSUMER_STARTED,
            MODALITY_TAGS("consumer"),
            "Measurement consumer started");
    assert(err == MODALITY_PROBE_ERROR_OK);
}

static void deinit_consumer(void)
{
    size_t err;

    err = MODALITY_PROBE_RECORD(
            g_consumer_probe,
            CONSUMER_SHUTDOWN,
            MODALITY_TAGS("consumer"),
            "Measurement consumer shutting down");
    assert(err == MODALITY_PROBE_ERROR_OK);

    send_report(g_consumer_probe);
}

static void run_consumer(void)
{
    size_t err;
    measurement_s measurement;

    const modality_probe_instant now = modality_probe_now(g_consumer_probe);
    syslog(
            LOG_INFO,
            "Consumer now "
            "(id: %" PRIu32 ", epoch: %" PRIu16 ", ticks: %" PRIu16 ", event_count: %" PRIu32 ")\n",
            now.clock.id,
            now.clock.epoch,
            now.clock.ticks,
            now.event_count);

    if(g_measurement_queue != NULL)
    {
        (void) memcpy(&measurement, g_measurement_queue, sizeof(measurement));
        g_measurement_queue = NULL;

        err = modality_probe_merge_snapshot(
                g_consumer_probe,
                &measurement.snapshot);
        assert(err == MODALITY_PROBE_ERROR_OK);

        err = MODALITY_PROBE_RECORD_W_I8(
                g_consumer_probe,
                CONSUMER_MEASUREMENT_RECVD,
                measurement.m,
                MODALITY_TAGS("consumer", "measurement", "receive"),
                "Measurement consumer recvd a new value");
        assert(err == MODALITY_PROBE_ERROR_OK);

        printf("Consumer recvd %" PRIi8 "\n", measurement.m);
    }
}

int main(int argc, char **argv)
{
    time_t t;
    srand((unsigned int) time(&t));

    openlog("c-example", LOG_NDELAY | LOG_PID, LOG_USER);

    (void) memset(&g_collector_addr, 0, sizeof(g_collector_addr));
    g_collector_addr.sin_family = AF_INET;
    g_collector_addr.sin_port = htons(COLLECTOR_PORT);
    g_collector_addr.sin_addr.s_addr = inet_addr(COLLECTOR_ADDRESS);

    g_report_socket = socket(AF_INET, SOCK_DGRAM, 0);
    assert(g_report_socket != -1);

    printf("Modality probe reports will be sent to %s:%u\n", COLLECTOR_ADDRESS, COLLECTOR_PORT);

    init_producer();

    init_consumer();

    run_producer();

    run_consumer();

    printf("Shutting down\n");

    deinit_producer();
    deinit_consumer();

    (void) close(g_report_socket);

    printf("All done\n");

    return EXIT_SUCCESS;
}
