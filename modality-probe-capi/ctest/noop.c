#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MODALITY_PROBE_MACROS_ENABLED 0 /* Turn the macros into no-ops */
#include "probe.h"

#define DEFAULT_PROBE_SIZE (1024)
#define DEFAULT_PROBE_ID (1)
#define EVENT_A (100)

static modality_probe *g_probe = MODALITY_PROBE_NULL_INITIALIZER;
static uint8_t g_storage[DEFAULT_PROBE_SIZE];

int main(void) {
    size_t err;
    err = MODALITY_PROBE_INIT(
            &g_storage[0],
            DEFAULT_PROBE_SIZE,
            DEFAULT_PROBE_ID,
            0,
            0,
            NULL,
            NULL,
            &g_probe,
            MODALITY_TAGS("my-tags", "more tags"),
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD(
            g_probe,
            EVENT_A,
            MODALITY_TAGS(network, file-system, "other-tags"),
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD(
            g_probe,
            EVENT_A,
            MODALITY_TAGS(network, file-system, "other-tags"));
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD(
            g_probe,
            EVENT_A,
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD(g_probe, EVENT_A);
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD_W_TIME(
            g_probe,
            EVENT_A,
            1,
            MODALITY_TAGS(network, file-system, "other-tags"),
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);

    const uint8_t my_data = 12;
    err = MODALITY_PROBE_RECORD_W_U8(g_probe, EVENT_A, my_data);
    err = MODALITY_PROBE_RECORD_W_U8_W_TIME(g_probe, EVENT_A, my_data, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U8(
            g_probe,
            EVENT_A,
            my_data,
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U8(
            g_probe,
            EVENT_A,
            my_data,
            MODALITY_TAGS("thing1", "thing2"));
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U8(
            g_probe,
            EVENT_A,
            my_data,
            MODALITY_TAGS("thing1", "thing2"),
            "Description");
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD_W_I8(g_probe, EVENT_A, 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_I16(g_probe, EVENT_A, 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U16(g_probe, EVENT_A, 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_I32(g_probe, EVENT_A, 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U32(g_probe, EVENT_A, 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_BOOL(g_probe, EVENT_A, false);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_F32(g_probe, EVENT_A, 0.0f);
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_RECORD_W_I8_W_TIME(g_probe, EVENT_A, 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_I16_W_TIME(g_probe, EVENT_A, 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U16_W_TIME(g_probe, EVENT_A, 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_I32_W_TIME(g_probe, EVENT_A, 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_U32_W_TIME(g_probe, EVENT_A, 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_BOOL_W_TIME(g_probe, EVENT_A, false, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_RECORD_W_F32_W_TIME(g_probe, EVENT_A, 0.0f, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_EXPECT(g_probe, EVENT_A, 1 == 0);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_EXPECT(g_probe, EVENT_A, 1 == 0, MODALITY_SEVERITY(2));
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_EXPECT_W_TIME(g_probe, EVENT_A, 1 == 0, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);

    err = MODALITY_PROBE_FAILURE(g_probe, EVENT_A);
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_FAILURE(g_probe, EVENT_A, MODALITY_SEVERITY(3));
    assert(err == MODALITY_PROBE_ERROR_OK);
    err = MODALITY_PROBE_FAILURE_W_TIME(g_probe, EVENT_A, 1);
    assert(err == MODALITY_PROBE_ERROR_OK);

    return 0;
}
