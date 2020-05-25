#ifndef EKOTRACE_H
#define EKOTRACE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

#define EKOTRACE_NULL_TRACER_INITIALIZER (NULL)

/*
 * Ekotrace is the type of a tracing instance. Expected to be single-threaded.
 */
typedef struct ekotrace ekotrace;

typedef struct logical_clock {
    /*
     * The ekotrace node that this clock is tracking
     */
    uint32_t id;
    /*
     *Clock tick count
     */
    uint32_t count;
} logical_clock;

typedef struct ekotrace_instant {
    /*
     * The current location's logical clock.
     * `clock.id` should be equivalent to the id
     * (a.k.a TracerId or location id) of the source `Ekotrace` instance
     */
    logical_clock clock;
    /*
     * How many events have been seen since the source instance
     * reached the associated `clock`'s point in causal
     * time.
     */
    uint32_t event_count;
} ekotrace_instant;

typedef uint16_t chunked_report_token;

typedef enum {
    /*
     * Everything is okay
     */
    EKOTRACE_RESULT_OK = 0,
    /*
     * A null pointer was provided to the function
     */
    EKOTRACE_RESULT_NULL_POINTER = 1,
    /*
     * An event id outside of the allowed range was provided.
     */
    EKOTRACE_RESULT_INVALID_EVENT_ID = 2,
    /*
     * A ekotrace id outside of the allowed range was provided.
     */
    EKOTRACE_RESULT_INVALID_TRACER_ID = 3,
    /*
     * The size available for output bytes was insufficient
     * to store a valid representation.
     */
    EKOTRACE_RESULT_INSUFFICIENT_DESTINATION_BYTES = 4,
    /*
     * Bumped into a pointer size limitation
     */
    EKOTRACE_RESULT_EXCEEDED_MAXIMUM_ADDRESSABLE_SIZE = 5,
    /*
     * An unexpected error in internal data encoding occurred.
     */
    EKOTRACE_RESULT_INTERNAL_ENCODING_ERROR = 6,
    /*
     * The local ekotrace does not have enough space to track all
     * of direct neighbors attempting to communicate with it.
     * Detected during merging.
     */
    EKOTRACE_RESULT_EXCEEDED_AVAILABLE_CLOCKS = 7,

    /*
     * The external history we attempted to merge was encoded
     * in an invalid fashion.
     * Detected during merging.
     */
    EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_ENCODING = 8,
    /*
     * The provided external history violated a semantic rule of the protocol,
     * such as by having a ekotrace_id out of the allowed value range.
     * Detected during merging.
     */
    EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS = 9,
    /*
     * The tracer encountered a problem dealing with extension metadata
     */
    EKOTRACE_RESULT_EXTENSION_ERROR = 10,
    /*
     * The tracer attempted to mutate internal state while
     * a report lock was active.
     */
    EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR = 11,
    /*
     * The tracer attempted to do a chunked report operation when no
     * chunked report has been started.
     */
    EKOTRACE_RESULT_NO_CHUNKED_REPORT_IN_PROGRESS = 12,
} ekotrace_result;

typedef struct causal_snapshot {
    /*
     * What ekotrace instance produced this history snapshot.
     * Not included in causal ordering evaluation.
     */
    uint32_t tracer_id;

    /*
     * Mapping between ekotrace_ids and event-counts at each location
     */
    logical_clock clocks[256];

    /*
     * How many of those clocks are actually populated
     */
    uint8_t clocks_len;
} causal_snapshot;

/*
 * Ekotrace event recording macro.
 *
 * Used to expose event recording information to the CLI tooling.
 *
 * Expands to call `ekotrace_record_event(ekt, event)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - A string for declaring tags: "tags=<tag>[;<tag>]"
 * - A string for the event description
 *
 */
#define EKOTRACE_RECORD(ekt, event, ...) \
        ekotrace_record_event(ekt, event)

/*
 * Ekotrace event recording with payload macro.
 *
 * Used to expose event recording information to the CLI tooling.
 *
 * Expands to call `ekotrace_record_event_with_payload_<type>(ekt, event)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - A string for declaring tags: "tags=<tag>[;<tag>]"
 * - A string for the event description
 *
 */
#define EKOTRACE_RECORD_W_I8(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_i8(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_U8(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_u8(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_I16(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_i16(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_U16(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_u16(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_I32(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_i32(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_U32(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_u32(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_BOOL(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_bool(\
            ekt, \
            event, \
            payload)
#define EKOTRACE_RECORD_W_F32(ekt, event, payload, ...) \
    ekotrace_record_event_with_payload_f32(\
            ekt, \
            event, \
            payload)

/*
 * Create a ekotrace instance. ekotrace_id must be non-zero
 */
size_t ekotrace_initialize(uint8_t *destination, size_t destination_size_bytes, uint32_t ekotrace_id, ekotrace * * out);

/*
 * Record an event.
 * event_id must be non-zero.
 */
size_t ekotrace_record_event(ekotrace *ekotrace, uint32_t event_id);

/*
 * Record an event along with a 4-byte payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload(ekotrace *ekotrace, uint32_t event_id, uint32_t payload);

/*
 * Record an event along with a i8 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_i8(ekotrace *ekotrace, uint32_t event_id, int8_t payload);

/*
 * Record an event along with a u8 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_u8(ekotrace *ekotrace, uint32_t event_id, uint8_t payload);

/*
 * Record an event along with a i16 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_i16(ekotrace *ekotrace, uint32_t event_id, int16_t payload);

/*
 * Record an event along with a u16 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_u16(ekotrace *ekotrace, uint32_t event_id, uint16_t payload);

/*
 * Record an event along with a i32 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_i32(ekotrace *ekotrace, uint32_t event_id, int32_t payload);

/*
 * Record an event along with a u32 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_u32(ekotrace *ekotrace, uint32_t event_id, uint32_t payload);

/*
 * Record an event along with a bool payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_bool(ekotrace *ekotrace, uint32_t event_id, bool payload);

/*
 * Record an event along with a f32 payload.
 *
 * event_id must be non-zero.
 */
size_t ekotrace_record_event_with_payload_f32(ekotrace *ekotrace, uint32_t event_id, float payload);

/*
 * Conduct necessary background activities, then
 * write a report of recorded events and logical clock
 * data to a supplied destination.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
size_t ekotrace_report(ekotrace *ekotrace, uint8_t *log_report_destination, size_t log_report_destination_bytes, size_t * out_written_bytes);

/*
 * Produce a transmittable opaque blob of this ekotrace's
 * causal history for use by another ekotrace elsewhere
 * in the system, filtered down to just the history
 * of this node and its immediate inbound neighbors.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
size_t ekotrace_distribute_snapshot(ekotrace *ekotrace, uint8_t *history_destination, size_t history_destination_bytes, size_t * out_written_bytes);

/*
 * Produce a transmittable summary of this ekotrace's
 * causal history for use by another ekotrace elsewhere
 * in the system, filtered down to just the history
 * of this node and its immediate inbound neighbors.
 */
size_t ekotrace_distribute_fixed_size_snapshot(ekotrace *ekotrace, causal_snapshot *snapshot);

/*
 * Consume an opaque causal history snapshot blob provided
 * by some other Ekotrace instance via ekotrace_distribute_snapshot.
 */
size_t ekotrace_merge_snapshot(ekotrace *ekotrace, uint8_t *history_source, size_t history_source_bytes);

/*
 * Consume a fixed-size causal history summary structure provided
 * by some other Ekotrace.
 */
size_t ekotrace_merge_fixed_size_snapshot(ekotrace *ekotrace, causal_snapshot *snapshot);

/*
 * Capture the ekotrace instance's moment in causal time
 * for correlation with external systems.
 *
 * If the pointer to the ekotrace instance (a.k.a. tracer) was null,
 * returns an `ekotrace_instant` with its `clock.id` value
 * set to the invalid location id `0`.
 */
ekotrace_instant ekotrace_now(ekotrace *ekotrace);

/*
 * Prepare to write a chunked report.
 *
 * Populates the out-parameter `out_report_token` with
 * a value that will be used to produce the
 * chunks for the report in calls to
 * `ekotrace_write_next_report_chunk` and `ekotrace_finish_chunked_report`
 *
 * Once this method has been called, mutating operations on
 * the Ekotrace instance will return `EKOTRACE_RESULT_REPORT_LOCK_CONFLICT_ERROR`
 * until all available chunks have been written with  `ekotrace_write_next_report_chunk`
 * and `ekotrace_finish_chunked_report` called.
 */
size_t ekotrace_start_chunked_report(ekotrace *ekotrace, chunked_report_token *out_report_token);

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
 * The provided `chunked_report_token` should match the value
 * populated by the `ekotrace_start_chunked_report` call
 * at the start of this chunked report.
 */
size_t ekotrace_write_next_report_chunk(ekotrace *ekotrace, chunked_report_token *report_token, uint8_t *log_report_destination, size_t log_report_destination_bytes, size_t *out_written_bytes);

/*
 * Necessary clean-up and finishing step at the end
 * of iterating through a chunked report.
 *
 * The provided ChunkedReportToken should match the value
 * populated by the `ekotrace_start_chunked_report` call
 * at the start of this chunked report.
 */
size_t ekotrace_finish_chunked_report(ekotrace *ekotrace, chunked_report_token *report_token);

#ifdef __cplusplus
} // extern "C"
#endif


#endif /* EKOTRACE_H */
