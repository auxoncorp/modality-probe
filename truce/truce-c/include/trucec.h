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


typedef bool (*SendToBackendFn)(void *state, const uint8_t *data, size_t len);

/*
 * Wrapper around user-defined function pointer and state blob for sending
 * trace data to the backend.
 */
typedef struct trace_backend {
    void * state;
    SendToBackendFn send_fn;
} trace_backend;

/*
 * Create a tracer instance. tracer_id must be non-zero
 */
tracer * tracer_initialize(uint8_t *destination, size_t destination_size_bytes, uint32_t tracer_id, trace_backend *backend);

/*
 * Record an event.
 * event_id must be non-zero.
 */
void tracer_record_event(tracer *tracer, uint32_t event_id);

/*
 * Conduct necessary background activities, such as transmission
 * of the the recorded events to a collection backend or
 * optimization of local data.
 */
void tracer_service(tracer *tracer);

/*
 * Produce a transmittable summary of this tracer's
 * causal history for use by another tracer elsewhere
 * in the system, filtered down to just the history
 * of this node and its immediate inbound neighbors.
 */
causal_snapshot tracer_snapshot(tracer *tracer);

/*
 * Consume a causal history summary structure provided
 * by some other Tracer.
 */
void tracer_merge_history(tracer *tracer, causal_snapshot *snapshot);

#ifdef __cplusplus
} // extern "C"
#endif
