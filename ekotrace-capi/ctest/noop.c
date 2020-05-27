#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define EKOTRACE_MACROS_ENABLED 0 /* Turn the macros into no-ops */
#include "ekotrace.h"

#define DEFAULT_TRACER_SIZE (1024)
#define DEFAULT_TRACER_ID (1)
#define EVENT_A (100)

static ekotrace *g_tracer = EKOTRACE_NULL_TRACER_INITIALIZER;
static uint8_t g_storage[DEFAULT_TRACER_SIZE];

int main(void) {
    size_t err;
    err = EKOTRACE_INITIALIZE(
            &g_storage[0],
            DEFAULT_TRACER_SIZE,
            DEFAULT_TRACER_ID,
            &g_tracer,
            "tags=my-tags;more tags",
            "Description");
    assert(err == EKOTRACE_RESULT_OK);

    err = EKOTRACE_RECORD(
            g_tracer,
            EVENT_A,
            "tags=network;file-system;other-tags",
            "Description");
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD(
            g_tracer,
            EVENT_A,
            "tags=network;file-system;other-tags");
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD(
            g_tracer,
            EVENT_A,
            "Description");
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD(g_tracer, EVENT_A);
    assert(err == EKOTRACE_RESULT_OK);

    const uint8_t my_data = 12;
    err = EKOTRACE_RECORD_W_U8(g_tracer, EVENT_A, my_data);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_U8(
            g_tracer,
            EVENT_A,
            my_data,
            "Description");
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_U8(
            g_tracer,
            EVENT_A,
            my_data,
            "tags=thing1;thing2");
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_U8(
            g_tracer,
            EVENT_A,
            my_data,
            "tags=thing1;thing2",
            "Description");
    assert(err == EKOTRACE_RESULT_OK);

    err = EKOTRACE_RECORD_W_I8(g_tracer, EVENT_A, 0);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_I16(g_tracer, EVENT_A, 0);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_U16(g_tracer, EVENT_A, 0);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_I32(g_tracer, EVENT_A, 0);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_U32(g_tracer, EVENT_A, 0);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_BOOL(g_tracer, EVENT_A, false);
    assert(err == EKOTRACE_RESULT_OK);
    err = EKOTRACE_RECORD_W_F32(g_tracer, EVENT_A, 0.0f);
    assert(err == EKOTRACE_RESULT_OK);

    return 0;
}
