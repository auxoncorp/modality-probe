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
static uint32_t DEFAULT_TRACER_ID = 314;
static uint32_t EVENT_A = 100;

bool test_backend_piping() {
    bool passed = true;
    counting_backend counter = { .count = 0 };
    trace_backend backend = trace_backend_new(update_counting_backend, &counter);
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * t = tracer_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &backend);
    tracer_service(t);
    if (counter.count != 1) {
        passed = false;
    }
    free(t);
    return passed;
}

typedef struct noop_backend {} noop_backend;

bool update_noop_backend(void *state, const uint8_t *data, size_t len) {
    return true;
}

bool test_event_recording() {
    bool passed = true;
    noop_backend noop = {  };
    trace_backend backend = trace_backend_new(update_noop_backend, &noop);
    uint8_t * destination = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * t = tracer_initialize(destination, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &backend);
    causal_snapshot snap_a = tracer_snapshot(t);
    if (snap_a.tracer_id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    if (snap_a.buckets_len != 0) {
        passed = false;
    }
    tracer_record_event(t, EVENT_A);
    causal_snapshot snap_b = tracer_snapshot(t);
    if (snap_b.buckets_len != 1) {
        passed = false;
    }

    free(t);
    return passed;
}
bool test_merge() {
    bool passed = true;
    noop_backend noop = {  };
    trace_backend backend = trace_backend_new(update_noop_backend, &noop);
    uint8_t * destination_a = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    tracer * tracer_a = tracer_initialize(destination_a, DEFAULT_TRACER_SIZE, DEFAULT_TRACER_ID, &backend);
    uint8_t * destination_b = (uint8_t*)malloc(DEFAULT_TRACER_SIZE);
    uint32_t tracer_b_id = DEFAULT_TRACER_ID + 1;
    tracer * tracer_b = tracer_initialize(destination_b, DEFAULT_TRACER_SIZE, tracer_b_id, &backend);
    tracer_record_event(tracer_a, EVENT_A);
    causal_snapshot snap_a = tracer_snapshot(tracer_a);
    tracer_merge_history(tracer_b, &snap_a);
    causal_snapshot snap_b = tracer_snapshot(tracer_b);
    if (snap_b.buckets_len != 1) {
        passed = false;
    }
    if (snap_b.buckets[0].id != DEFAULT_TRACER_ID) {
        passed = false;
    }
    tracer_record_event(tracer_b, EVENT_A);
    causal_snapshot snap_c = tracer_snapshot(tracer_b);
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
