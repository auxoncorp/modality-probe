#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Tracer is the type of a tracing instance. Expected to be single-threaded.
 */
typedef struct tracer tracer;

typedef struct logical_clock_bucket {
    /*
     * The tracer node that this clock is tracking
     */
    uint32_t id;
    /*
     *Clock tick count
     */
    uint32_t count;
} logical_clock_bucket;

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
     * A tracer id outside of the allowed range was provided.
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
     * The local tracer does not have enough space to track all
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
     * such as by having a tracer_id out of the allowed value range.
     * Detected during merging.
     */
    EKOTRACE_RESULT_INVALID_EXTERNAL_HISTORY_SEMANTICS = 9,
} ekotrace_result;

typedef struct causal_snapshot {
    /*
     * What tracer produced this history snapshot.
     * Not included in causal ordering evaluation.
     */
    uint32_t tracer_id;

    /*
     * Mapping between tracer_ids and event-counts at each location
     */
    logical_clock_bucket buckets[256];

    /*
     * How many of those buckets are actually populated
     */
    uint8_t buckets_len;
} causal_snapshot;

/*
 * Create a tracer instance. tracer_id must be non-zero
 */
ekotrace_result tracer_initialize(uint8_t *destination, size_t destination_size_bytes, uint32_t tracer_id, tracer * * out);

/*
 * Record an event.
 * event_id must be non-zero.
 */
ekotrace_result tracer_record_event(tracer *tracer, uint32_t event_id);

/*
 * Conduct necessary background activities, then
 * write recorded events and logical clock data to a
 * supplied destination.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
ekotrace_result tracer_write_log_report(tracer *tracer, uint8_t *log_report_destination, size_t log_report_destination_bytes, size_t * out_written_bytes);

/*
 * Produce a transmittable opaque blob of this tracer's
 * causal history for use by another tracer elsewhere
 * in the system, filtered down to just the history
 * of this node and its immediate inbound neighbors.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
ekotrace_result tracer_share_history(tracer *tracer, uint8_t *history_destination, size_t history_destination_bytes, size_t * out_written_bytes);

/*
 * Produce a transmittable summary of this tracer's
 * causal history for use by another tracer elsewhere
 * in the system, filtered down to just the history
 * of this node and its immediate inbound neighbors.
 */
ekotrace_result tracer_share_fixed_size_history(tracer *tracer, causal_snapshot *snapshot);

/*
 * Consume an opaque causal history blob provided
 * by some other Tracer.
 */
ekotrace_result tracer_merge_history(tracer *tracer, uint8_t *history_source, size_t history_source_bytes);

/*
 * Consume a fixed-size causal history summary structure provided
 * by some other Tracer.
 */
ekotrace_result tracer_merge_fixed_size_history(tracer *tracer, causal_snapshot *snapshot);

#ifdef __cplusplus
} // extern "C"
#endif
