#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "probe.h"

static size_t DEFAULT_PROBE_SIZE = 7000;
static size_t DEFAULT_LOG_STORAGE = 4096;
static size_t MAX_REPORT_CHUNK_SIZE = 256;
static uint32_t DEFAULT_PROBE_ID = 314;
static uint32_t EVENT_A = 100;

#define ERROR_CHECK(err, passed) \
    do { \
        if (err != MODALITY_PROBE_ERROR_OK) { \
            fprintf(stderr, "error check failed at line %d, err=%d\n", __LINE__, result); \
            passed = false; \
        }\
    } while(0)

bool test_backend_piping(void) {
    bool passed = true;
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe * t = MODALITY_PROBE_NULL_INITIALIZER;
    modality_probe_error result = modality_probe_initialize(destination, DEFAULT_PROBE_SIZE, DEFAULT_PROBE_ID, &t);
    ERROR_CHECK(result, passed);

    uint8_t * log_storage = (uint8_t*)malloc(DEFAULT_LOG_STORAGE);
    size_t bytes_written;
    result = modality_probe_report(t, log_storage, DEFAULT_LOG_STORAGE, &bytes_written);
    ERROR_CHECK(result, passed);
    if (bytes_written == 0) {
        passed = false;
    }
    bool all_zeros = true;
    unsigned int i;
    for (i = 0; i < DEFAULT_LOG_STORAGE; i++) {
        if (log_storage[i] != 0) {
            all_zeros = false;
            break;
        }
    }
    if (all_zeros) {
        passed = false;
    }
    free(destination);
    free(log_storage);
    return passed;
}

bool test_event_recording(void) {
    bool passed = true;
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe * t;
    modality_probe_error result = MODALITY_INITIALIZE(
            destination,
            DEFAULT_PROBE_SIZE,
            DEFAULT_PROBE_ID,
            &t,
            "tags=tag 1; tag 2",
            "desc");
    ERROR_CHECK(result, passed);

    modality_causal_snapshot snap_a;
    result = modality_probe_distribute_fixed_size_snapshot(t, &snap_a);
    ERROR_CHECK(result, passed);
    if (snap_a.probe_id != DEFAULT_PROBE_ID) {
        passed = false;
    }
    if (snap_a.clocks_len != 1) {
        passed = false;
    }
    result = modality_probe_record_event(t, EVENT_A);
    ERROR_CHECK(result, passed);
    result = modality_probe_record_event_with_payload(t, EVENT_A, 1);
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD(t, EVENT_A, (int8_t) 1, "tags=my-tag", "description");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD(t, EVENT_A, (int8_t) 1, "tags=my-tag");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_I8(t, EVENT_A, (int8_t) 1);
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_U8(t, EVENT_A, (uint8_t) 1, "more docs");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_I16(t, EVENT_A, (int16_t) 1, "tags=my tag");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_U16(t, EVENT_A, (uint16_t) 1, "tags=a-tag", "desc");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_I32(t, EVENT_A, (int32_t) 1, "some docs");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_U32(t, EVENT_A, (uint32_t) 1);
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_BOOL(t, EVENT_A, true, "my docs");
    ERROR_CHECK(result, passed);
    result = MODALITY_RECORD_W_F32(t, EVENT_A, 1.23f, "my docs");
    ERROR_CHECK(result, passed);
    result = MODALITY_EXPECT(t, EVENT_A, 1 == 0, "my docs", "tags=severity.10");
    ERROR_CHECK(result, passed);
    modality_causal_snapshot snap_b;
    result = modality_probe_distribute_fixed_size_snapshot(t, &snap_b);
    ERROR_CHECK(result, passed);
    if (snap_b.clocks_len != 1) {
        passed = false;
    }

    free(t);
    return passed;
}

bool test_merge(void) {
    bool passed = true;
    uint8_t * destination_a = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe * probe_a;
    modality_probe_error result = modality_probe_initialize(destination_a, DEFAULT_PROBE_SIZE, DEFAULT_PROBE_ID, &probe_a);
    ERROR_CHECK(result, passed);
    uint8_t * destination_b = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    uint32_t probe_b_id = DEFAULT_PROBE_ID + 1;
    modality_probe * probe_b;
    result = modality_probe_initialize(destination_b, DEFAULT_PROBE_SIZE, probe_b_id, &probe_b);
    ERROR_CHECK(result, passed);
    result = modality_probe_record_event(probe_a, EVENT_A);
    ERROR_CHECK(result, passed);
    modality_causal_snapshot snap_a;
    result = modality_probe_distribute_fixed_size_snapshot(probe_a, &snap_a);
    ERROR_CHECK(result, passed);
    if (snap_a.clocks_len != 1) {
        passed = false;
    }
    if (snap_a.clocks[0].id != DEFAULT_PROBE_ID) {
        passed = false;
    }
    result = modality_probe_merge_fixed_size_snapshot(probe_b, &snap_a);
    ERROR_CHECK(result, passed);
    modality_causal_snapshot snap_b;
    result = modality_probe_distribute_fixed_size_snapshot(probe_b, &snap_b);
    ERROR_CHECK(result, passed);
    if (snap_b.clocks_len != 2 || snap_b.clocks[0].id != probe_b_id || snap_b.clocks[1].id != DEFAULT_PROBE_ID) {
        passed = false;
    }
    result = modality_probe_record_event(probe_b, EVENT_A);
    ERROR_CHECK(result, passed);
    modality_causal_snapshot snap_c;
    result = modality_probe_distribute_fixed_size_snapshot(probe_b, &snap_c);
    ERROR_CHECK(result, passed);
    if (snap_c.clocks_len != 2 || snap_c.clocks[0].id != probe_b_id || snap_c.clocks[1].id != DEFAULT_PROBE_ID) {
        passed = false;
    }

    free(probe_a);
    free(probe_b);
    return passed;
}

bool test_now(void) {
    bool passed = true;
    uint8_t * destination_a = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe * probe_a;
    modality_probe_error result = modality_probe_initialize(destination_a, DEFAULT_PROBE_SIZE, DEFAULT_PROBE_ID, &probe_a);
    ERROR_CHECK(result, passed);
    modality_probe_instant instant_a = modality_probe_now(probe_a);
    /* modality_probe_instant should have the correct id and start at 0 logical clock count and 0 event count */
    if (instant_a.clock.id != DEFAULT_PROBE_ID || instant_a.clock.count != 0 || instant_a.event_count != 0) {
        passed = false;
    }

    uint8_t * destination_b = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    uint32_t probe_b_id = DEFAULT_PROBE_ID + 1;
    modality_probe * probe_b;
    result = modality_probe_initialize(destination_b, DEFAULT_PROBE_SIZE, probe_b_id, &probe_b);
    ERROR_CHECK(result, passed);

    /* Recording an event should tick the event_count of the seen instant */
    result = modality_probe_record_event(probe_a, EVENT_A);
    ERROR_CHECK(result, passed);
    instant_a = modality_probe_now(probe_a);
    if (instant_a.clock.id != DEFAULT_PROBE_ID || instant_a.clock.count != 0 || instant_a.event_count != 1) {
        passed = false;
    }
    /* Recording an event should tick the event_count of the seen instant */
    result = modality_probe_record_event(probe_a, EVENT_A);
    ERROR_CHECK(result, passed);
    instant_a = modality_probe_now(probe_a);
    if (instant_a.clock.id != DEFAULT_PROBE_ID || instant_a.clock.count != 0 || instant_a.event_count != 2) {
        passed = false;
    }
    modality_causal_snapshot snap_a;
    result = modality_probe_distribute_fixed_size_snapshot(probe_a, &snap_a);
    ERROR_CHECK(result, passed);
    /*
     * When the logical clock ticks up, here because we distributed a snapshot
     * the event_count should reset to 0
     */
    instant_a = modality_probe_now(probe_a);
    if (instant_a.clock.id != DEFAULT_PROBE_ID || instant_a.clock.count != 1 || instant_a.event_count != 0) {
        passed = false;
    }

    modality_probe_instant instant_b = modality_probe_now(probe_b);
    if (instant_b.clock.id != probe_b_id || instant_b.clock.count != 0 || instant_b.event_count != 0) {
        passed = false;
    }
    modality_probe_merge_fixed_size_snapshot(probe_b, &snap_a);
    instant_b = modality_probe_now(probe_b);
    if (instant_b.clock.id != probe_b_id || instant_b.clock.count != 1 || instant_b.event_count != 0) {
        passed = false;
    }
    modality_causal_snapshot snap_b;
    result = modality_probe_distribute_fixed_size_snapshot(probe_b, &snap_b);
    ERROR_CHECK(result, passed);
    instant_b = modality_probe_now(probe_b);
    if (instant_b.clock.id != probe_b_id || instant_b.clock.count != 2 || instant_b.event_count != 0) {
        passed = false;
    }
    result = modality_probe_record_event(probe_b, EVENT_A);
    ERROR_CHECK(result, passed);
    instant_b = modality_probe_now(probe_b);
    if (instant_b.clock.id != probe_b_id || instant_b.clock.count != 2 || instant_b.event_count != 1) {
        passed = false;
    }

    uint8_t * log_storage = (uint8_t*)malloc(DEFAULT_LOG_STORAGE);
    size_t bytes_written;
    result = modality_probe_report(probe_b, log_storage, DEFAULT_LOG_STORAGE, &bytes_written);
    ERROR_CHECK(result, passed);
    instant_b = modality_probe_now(probe_b);
    if (instant_b.clock.id != probe_b_id) {
        passed = false;
    }
    if (instant_b.clock.count != 3) {
        passed = false;
    }
    /*
     * Note that the event count is 1 after a report call because ModalityProbe
     * internally records an event after producing a report.
     */
    if (instant_b.event_count != 1) {
        passed = false;
    }

    free(probe_a);
    free(probe_b);
    return passed;
}

bool test_chunked_reporting(void) {
    bool passed = true;
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_PROBE_SIZE);
    modality_probe * t = MODALITY_PROBE_NULL_INITIALIZER;
    modality_probe_error result = modality_probe_initialize(destination, DEFAULT_PROBE_SIZE, DEFAULT_PROBE_ID, &t);
    ERROR_CHECK(result, passed);

    uint8_t * log_storage = (uint8_t*)malloc(MAX_REPORT_CHUNK_SIZE);
    modality_chunked_report_token report_token;
    result = modality_probe_start_chunked_report(t, &report_token);
    ERROR_CHECK(result, passed);

    size_t bytes_written;
    result = modality_probe_write_next_report_chunk(t, &report_token, log_storage, MAX_REPORT_CHUNK_SIZE, &bytes_written);
    ERROR_CHECK(result, passed);
    if (bytes_written == 0) {
        passed = false;
    }
    bool all_zeros = true;
    unsigned int i;
    for (i = 0; i < DEFAULT_LOG_STORAGE; i++) {
        if (log_storage[i] != 0) {
            all_zeros = false;
            break;
        }
    }
    if (all_zeros) {
        passed = false;
    }

    result = modality_probe_write_next_report_chunk(t, &report_token, log_storage, MAX_REPORT_CHUNK_SIZE, &bytes_written);
    ERROR_CHECK(result, passed);
    /* Expect the earlier chunk to suffice, so this should be empty */
    if (bytes_written != 0) {
        passed = false;
    }
    result = modality_probe_finish_chunked_report(t, &report_token);
    ERROR_CHECK(result, passed);

    free(destination);
    free(log_storage);
    return passed;
}

void run_test(bool (test)(void), const char *name, bool *passed) {
    if (!test()) {
        *passed = false;
        fprintf(stderr, "FAILED: %s\n", name);
    } else {
        fprintf(stderr, "PASSED: %s\n", name);
    }
}

int main(void) {
    bool passed = true;

    run_test(test_backend_piping, "test_backend_piping", &passed);
    run_test(test_event_recording, "test_event_recording", &passed);
    run_test(test_merge, "test_merge", &passed);
    run_test(test_now, "test_now", &passed);
    run_test(test_chunked_reporting, "test_chunked_reporting", &passed);
    if (!passed) {
        fprintf(stderr, "FAILED c test suite\n");
        exit(1);
    }
    fprintf(stderr, "PASSED c test suite\n");
    return 0;
}
