#ifndef MODALITY_PROBE_H
#define MODALITY_PROBE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Modality probe macros are enabled by default.
 *
 * They can be made into no-op's by defining MODALITY_PROBE_MACROS_ENABLED=0.
 */
#ifndef MODALITY_PROBE_MACROS_ENABLED
#define MODALITY_PROBE_MACROS_ENABLED 1
#endif

#define MODALITY_PROBE_NULL_INITIALIZER (NULL)

/*
 * Modality probe is the type of a probe instance. Expected to be single-threaded.
 */
typedef struct modality_probe modality_probe;

typedef struct modality_logical_clock {
    /*
     * The Modality probe that this clock is tracking
     */
    uint32_t id;

    /*
     * Clock epoch
     */
    uint16_t epoch;

    /*
     * Clock tick count
     */
    uint16_t clock;
} modality_logical_clock;

typedef struct modality_probe_instant {
    /*
     * The current probe's logical clock.
     * `clock.id` should be equivalent to the probe id
     * of the source `ModalityProbe` instance
     */
    modality_logical_clock clock;
    /*
     * How many events have been seen since the source instance
     * reached the associated `clock`'s point in causal
     * time.
     */
    uint32_t event_count;
} modality_probe_instant;

typedef struct modality_causal_snapshot {
    /*
     * Probe id and tick-count at the probe which this history snapshot
     * was created from
     */
    modality_logical_clock clock;
    /*
     * Reserved field.
     */
    uint16_t reserved_0;
    /*
     * Reserved field.
     */
    uint16_t reserved_1;
} modality_causal_snapshot;

typedef uint16_t modality_chunked_report_token;

typedef enum {
    /*
     * Everything is okay
     */
    MODALITY_PROBE_ERROR_OK = 0,
    /*
     * A null pointer was provided to the function
     */
    MODALITY_PROBE_ERROR_NULL_POINTER = 1,
    /*
     * An event id outside of the allowed range was provided.
     */
    MODALITY_PROBE_ERROR_INVALID_EVENT_ID = 2,
    /*
     * A probe id outside of the allowed range was provided.
     */
    MODALITY_PROBE_ERROR_INVALID_PROBE_ID = 3,
    /*
     * The size available for output bytes was insufficient
     * to store a valid representation.
     */
    MODALITY_PROBE_ERROR_INSUFFICIENT_DESTINATION_BYTES = 4,
    /*
     * Bumped into a pointer size limitation
     */
    MODALITY_PROBE_ERROR_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE = 5,
    /*
     * An unexpected error in internal data encoding occurred.
     */
    MODALITY_PROBE_ERROR_INTERNAL_ENCODING_ERROR = 6,
    /*
     * The local probe does not have enough space to track all
     * of direct neighbors attempting to communicate with it.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS = 7,
    /*
     * The the external history source buffer we attempted to merge
     * was insufficiently sized for a valid causal snapshot.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_INSUFFICIENT_SOURCE_BYTES = 8,
    /*
     * The provided external history violated a semantic rule of the protocol,
     * such as by having a probe_id out of the allowed value range.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS = 9,
    /*
     * The probe encountered a problem dealing with extension metadata
     */
    MODALITY_PROBE_ERROR_EXTENSION_ERROR = 10,
    /*
     * The probe attempted to mutate internal state while
     * a report lock was active.
     */
    MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR = 11,
    /*
     * The probe attempted to do a chunked report operation when no
     * chunked report has been started.
     */
    MODALITY_PROBE_ERROR_NO_CHUNKED_REPORT_IN_PROGRESS = 12,
} modality_probe_error;

/*
 * Modality probe tags specifying macro.
 *
 * This is a no-op macro used to expose tags to the CLI tooling.
 *
 * Note that tag strings must not contain any `(` or `)` characters.
 *
 * Example use:
 * ```c
 * MODALITY_TAGS(some tag)
 *
 * MODALITY_TAGS(tag-1, tag 2, "tag 3")
 * ```
 *
 */
#define MODALITY_TAGS(...)

/*
 * Modality probe instance initializer macro.
 *
 * Used to expose probe information to the CLI tooling.
 *
 * Expands to call `modality_probe_initialize(dest, dest_size, probe_id, probe)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the probe description
 *
 */
#define MODALITY_PROBE_INIT(dest, dest_size, probe_id, probe, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_initialize(dest, dest_size, probe_id, probe) : MODALITY_PROBE_ERROR_OK)

/*
 * Modality probe event recording macro.
 *
 * Used to expose event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record_event(probe, event)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the event description
 *
 */
#define MODALITY_PROBE_RECORD(probe, event, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event(probe, event) : MODALITY_PROBE_ERROR_OK)

/*
 * Modality probe event recording with payload macro.
 *
 * Used to expose event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record_event_with_payload_<type>(probe, event)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the event description
 *
 */
#define MODALITY_PROBE_RECORD_W_I8(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i8(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U8(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u8(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_I16(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i16(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U16(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u16(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_I32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_BOOL(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_bool(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_F32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_f32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)

/*
 * Modality probe expectation expression event recording macro.
 *
 * Used to expose expectation event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record_event_with_payload_u32(probe, event, expression_outcome)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the event description
 *
 */
#define MODALITY_PROBE_EXPECT(probe, event, expr, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u32(\
            probe, \
            event, \
            (expr)) : MODALITY_PROBE_ERROR_OK)

/*
 * Create a Modality probe instance. probe_id must be non-zero
 */
size_t modality_probe_initialize(
        uint8_t *destination,
        size_t destination_size_bytes,
        uint32_t probe_id,
        modality_probe **out);

/*
 * Record an event.
 * event_id must be non-zero.
 */
size_t modality_probe_record_event(
        modality_probe *probe,
        uint32_t event_id);

/*
 * Record an event along with a 4-byte payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload(
        modality_probe *probe,
        uint32_t event_id,
        uint32_t payload);

/*
 * Record an event along with a i8 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i8(
        modality_probe *probe,
        uint32_t event_id,
        int8_t payload);

/*
 * Record an event along with a u8 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u8(
        modality_probe *probe,
        uint32_t event_id,
        uint8_t payload);

/*
 * Record an event along with a i16 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i16(
        modality_probe *probe,
        uint32_t event_id,
        int16_t payload);

/*
 * Record an event along with a u16 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u16(
        modality_probe *probe,
        uint32_t event_id,
        uint16_t payload);

/*
 * Record an event along with a i32 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i32(
        modality_probe *probe,
        uint32_t event_id,
        int32_t payload);

/*
 * Record an event along with a u32 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u32(
        modality_probe *probe,
        uint32_t event_id,
        uint32_t payload);

/*
 * Record an event along with a bool payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_bool(
        modality_probe *probe,
        uint32_t event_id,
        bool payload);

/*
 * Record an event along with a f32 payload.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_f32(
        modality_probe *probe,
        uint32_t event_id,
        float payload);

/*
 * Conduct necessary background activities, then
 * write a report of recorded events and logical clock
 * data to a supplied destination.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
size_t modality_probe_report(
        modality_probe *probe,
        uint8_t *log_report_destination,
        size_t log_report_destination_bytes,
        size_t *out_written_bytes);

/*
 * Produce a transmittable summary of this Modality probe's
 * causal history for use by another Modality probe elsewhere
 * in the system.
 */
size_t modality_probe_produce_snapshot(
        modality_probe *probe,
        modality_causal_snapshot *snapshot);

/*
 * Produce a transmittable opaque blob of this Modality probe's
 * causal history for use by another Modality probe elsewhere
 * in the system.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
size_t modality_probe_produce_snapshot_bytes(
        modality_probe *probe,
        uint8_t *history_destination,
        size_t history_destination_bytes,
        size_t *out_written_bytes);

/*
 * Consume a causal history summary structure provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot(
        modality_probe *probe,
        const modality_causal_snapshot *snapshot);

/*
 * Consume a opaque causal history blob provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot_bytes(
        modality_probe *probe,
        const uint8_t *history_source,
        size_t history_source_bytes);

/*
 * Capture the Modality probe instance's moment in causal time
 * for correlation with external systems.
 *
 * If the pointer to the Modality probe instance (a.k.a. probe) was null,
 * returns an `modality_probe_instant` with its `clock.id` value
 * set to the invalid probe id `0`.
 */
modality_probe_instant modality_probe_now(
        modality_probe *probe);

/*
 * Prepare to write a chunked report.
 *
 * Populates the out-parameter `out_report_token` with
 * a value that will be used to produce the
 * chunks for the report in calls to
 * `modality_probe_write_next_report_chunk` and `modality_probe_finish_chunked_report`
 *
 * Once this method has been called, mutating operations on
 * the Modality probe instance will return `MODALITY_PROBE_ERROR_REPORT_LOCK_CONFLICT_ERROR`
 * until all available chunks have been written with  `modality_probe_write_next_report_chunk`
 * and `modality_probe_finish_chunked_report` called.
 */
size_t modality_probe_start_chunked_report(
        modality_probe *probe,
        modality_chunked_report_token *out_report_token);

/*
 * Write up to 1 chunk of a report into
 * the provided destination buffer.
 *
 * Populates the out-parameter `out_written_bytes` with
 * the number of report bytes written into the destination.
 *
 * If the `out_written_bytes` == 0, then no chunk was
 * written and there are no chunks left in the report.
 *
 * The provided `modality_chunked_report_token` should match the value
 * populated by the `modality_probe_start_chunked_report` call
 * at the start of this chunked report.
 */
size_t modality_probe_write_next_report_chunk(
        modality_probe *probe,
        const modality_chunked_report_token *report_token,
        uint8_t *log_report_destination,
        size_t log_report_destination_bytes,
        size_t *out_written_bytes);

/*
 * Necessary clean-up and finishing step at the end
 * of iterating through a chunked report.
 *
 * The provided ChunkedReportToken should match the value
 * populated by the `modality_probe_start_chunked_report` call
 * at the start of this chunked report.
 */
size_t modality_probe_finish_chunked_report(
        modality_probe *probe,
        const modality_chunked_report_token *report_token);

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* MODALITY_PROBE_H */
