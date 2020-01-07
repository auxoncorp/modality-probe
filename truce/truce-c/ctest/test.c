#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "trucec.h"

typedef struct counting_backend {
    uint32_t count;
} counting_backend;

bool update_counting_backend(void *state, const uint8_t *data, size_t len) {
    counting_backend * backend = state;
    backend->count = backend->count + 1;
    return true;
}

static size_t DEFAULT_TRACER_SIZE = 7000;
static size_t DEFAULT_LOG_STORAGE = 4096;
static uint32_t DEFAULT_TRACER_ID = 314;
static uint32_t EVENT_A = 100;

bool test_backend_piping() {
    bool passed = true;
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * t = tracer_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID);

    uint8_t * log_storage = (uint8_t*)malloc(DEFAULT_LOG_STORAGE);
    bool write_success = false;
    write_success = tracer_write_log_report(t, log_storage, DEFAULT_LOG_STORAGE);
    if (!write_success) {
        passed = false;
    }
    bool all_zeros = true;
    int i;
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

bool test_event_recording() {
    bool passed = true;
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * t = tracer_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID);

    causal_snapshot snap_a;
    bool make_snap_success = tracer_share_fixed_size_history(t, &snap_a);
    if (!make_snap_success) {
        passed = false;
    }
    if (snap_a.tracer_id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    if (snap_a.buckets_len != 1) {
        passed = false;
    }
    tracer_record_event(t, EVENT_A);
    causal_snapshot snap_b;
    make_snap_success = tracer_share_fixed_size_history(t, &snap_b);
    if (!make_snap_success) {
        passed = false;
    }
    if (snap_b.buckets_len != 1) {
        passed = false;
    }

    free(t);
    return passed;
}
bool test_merge() {
    bool passed = true;
    uint8_t * destination_a = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * tracer_a = tracer_initialize(destination_a, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID);
    uint8_t * destination_b = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    uint32_t tracer_b_id = DEFAULT_TRACER_ID + 1;
    tracer * tracer_b = tracer_initialize(destination_b, DEFAULT_TRACER_SIZE, tracer_b_id);
    tracer_record_event(tracer_a, EVENT_A);
    causal_snapshot snap_a;
    bool make_snap_success = tracer_share_fixed_size_history(tracer_a, &snap_a);
    if (!make_snap_success) {
        passed = false;
    }
    tracer_merge_fixed_size_history(tracer_b, &snap_a);
    causal_snapshot snap_b;
    make_snap_success = tracer_share_fixed_size_history(tracer_b, &snap_b);
    if (!make_snap_success) {
        passed = false;
    }
    if (snap_b.buckets_len != 1) {
        passed = false;
    }
    if (snap_b.buckets[0].id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    tracer_record_event(tracer_b, EVENT_A);
    causal_snapshot snap_c;
    make_snap_success = tracer_share_fixed_size_history(tracer_b, &snap_c);
    if (!make_snap_success) {
        passed = false;
    }
    if (snap_c.buckets_len != 2) {
        passed = false;
    }
    if (snap_b.buckets[0].id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    if (snap_b.buckets[1].id != tracer_b_id) {
        passed = false;
    }

    free(tracer_a);
    free(tracer_b);
    return passed;
}

void run_test(bool (test)(), const char *name, bool *passed) {
    if (!test()) {
        *passed = false;
        fprintf(stderr, "FAILED: %s\n", name);
    } else {
        fprintf(stderr, "PASSED: %s\n", name);
    }
}

int main() {
    bool passed = true;

    run_test(test_backend_piping, "test_backend_piping", &passed);
    run_test(test_event_recording, "test_event_recording", &passed);
    run_test(test_event_recording, "test_merge", &passed);
    if (!passed) {
        fprintf(stderr, "FAILED c test suite\n");
        exit(1);
    }
    fprintf(stderr, "PASSED c test suite\n");
    return 0;
}
