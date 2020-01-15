#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "ekotrace.h"

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
    ekotrace * t;
    ekotrace_result result = ekotrace_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &t);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }

    uint8_t * log_storage = (uint8_t*)malloc(DEFAULT_LOG_STORAGE);
    size_t bytes_written;
    result = ekotrace_report(t, log_storage, DEFAULT_LOG_STORAGE, &bytes_written);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    if (bytes_written == 0) {
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
    ekotrace * t;
    ekotrace_result result = ekotrace_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &t);
    if (result != EKOTRACE_RESULT_OK) {
        fprintf(stderr, "failed at initialization: %d\n", result);
        passed = false;
    }

    causal_snapshot snap_a;
    result = ekotrace_distribute_fixed_size_snapshot(t, &snap_a);
    if (result != EKOTRACE_RESULT_OK) {
        fprintf(stderr, "failed at shared fixed size: %d\n", result);
        passed = false;
    }
    if (snap_a.tracer_id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    if (snap_a.clocks_len != 1) {
        passed = false;
    }
    result = ekotrace_record_event(t, EVENT_A);
    if (result != EKOTRACE_RESULT_OK) {
        fprintf(stderr, "failed at record event: %d\n", result);
        passed = false;
    }
    causal_snapshot snap_b;
    result = ekotrace_distribute_fixed_size_snapshot(t, &snap_b);
    if (result != EKOTRACE_RESULT_OK) {
        fprintf(stderr, "failed at share fixed size history: %d\n", result);
        passed = false;
    }
    if (snap_b.clocks_len != 1) {
        passed = false;
    }

    free(t);
    return passed;
}
bool test_merge() {
    bool passed = true;
    uint8_t * destination_a = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    ekotrace * ekotrace_a;
    ekotrace_result result = ekotrace_initialize(destination_a, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &ekotrace_a);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    uint8_t * destination_b = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    uint32_t ekotrace_b_id = DEFAULT_TRACER_ID + 1;
    ekotrace * ekotrace_b;
    result = ekotrace_initialize(destination_b, DEFAULT_TRACER_SIZE, ekotrace_b_id, &ekotrace_b);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    ekotrace_record_event(ekotrace_a, EVENT_A);
    causal_snapshot snap_a;
    result = ekotrace_distribute_fixed_size_snapshot(ekotrace_a, &snap_a);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    ekotrace_merge_fixed_size_snapshot(ekotrace_b, &snap_a);
    causal_snapshot snap_b;
    result = ekotrace_distribute_fixed_size_snapshot(ekotrace_b, &snap_b);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    if (snap_b.clocks_len != 1) {
        passed = false;
    }
    if (snap_b.clocks[0].id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    ekotrace_record_event(ekotrace_b, EVENT_A);
    causal_snapshot snap_c;
    result = ekotrace_distribute_fixed_size_snapshot(ekotrace_b, &snap_c);
    if (result != EKOTRACE_RESULT_OK) {
        passed = false;
    }
    if (snap_c.clocks_len != 2) {
        passed = false;
    }
    if (snap_b.clocks[0].id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    if (snap_b.clocks[1].id != ekotrace_b_id) {
        passed = false;
    }

    free(ekotrace_a);
    free(ekotrace_b);
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
