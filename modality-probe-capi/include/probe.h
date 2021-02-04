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
 * This time domain is local to the probe only.
 */
#define MODALITY_PROBE_WALL_CLOCK_ID_LOCAL_ONLY (0)

/*
 * Unspecified wall clock time resolution.
 */
#define MODALITY_PROBE_TIME_RESOLUTION_UNSPECIFIED (0)

/*
 * Modality probe is the type of a probe instance. Expected to be single-threaded.
 */
typedef struct modality_probe modality_probe;

typedef struct modality_probe_logical_clock {
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
    uint16_t ticks;
} modality_probe_logical_clock;

typedef struct modality_probe_instant {
    /*
     * The current probe's logical clock.
     * `clock.id` should be equivalent to the probe id
     * of the source `ModalityProbe` instance
     */
    modality_probe_logical_clock clock;
    /*
     * How many events have been seen since the source instance
     * reached the associated `clock`'s point in causal
     * time.
     */
    uint32_t event_count;
} modality_probe_instant;

typedef struct modality_probe_causal_snapshot {
    /*
     * Probe id and tick-count at the probe which this history snapshot
     * was created from
     */
    modality_probe_logical_clock clock;
    /*
     * Reserved field.
     */
    uint8_t reserved_0[2];
    /*
     * Reserved field.
     */
    uint8_t reserved_1[2];
} modality_probe_causal_snapshot;

/*
 * Function type for retrieving the next persistent sequence number.
 *
 * This method is called when a probe initializes to get the initial
 * epoch portion of the clock, and each time the ticks portion of the
 * clock overflows during the probe's lifetime.
 *
 *
 * The function should return MODALITY_PROBE_ERROR_OK when the next
 * sequence value could be retrieved and was used to populate the
 * value at out_sequence_id.
 *
 * The sequence number starts at zero,
 * and be monotonically increased by a step size of one after each retrieval.
 *
 * When the sequence number reaches its maximum value (0xFFFF), it
 * should wrap around to the value 0.
 *
 * If no sequence number could be retrieved, the function should
 * return MODALITY_PROBE_ERROR_RESTART_PERSISTENCE_SEQUENCE_ID_UNAVAILABLE
 */
typedef size_t (*modality_probe_next_sequence_id_fn)(
        uint32_t probe_id,
        void *user_state,
        uint16_t *out_sequence_id);

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
     * The local probe does not have enough space to track all
     * of direct neighbors attempting to communicate with it.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_EXCEEDED_AVAILABLE_CLOCKS = 6,
    /*
     * The external history source buffer we attempted to merge
     * was insufficiently sized for a valid causal snapshot.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_INSUFFICIENT_SOURCE_BYTES = 7,
    /*
     * The provided external history violated a semantic rule of the protocol,
     * such as by having a probe_id out of the allowed value range.
     * Detected during merging.
     */
    MODALITY_PROBE_ERROR_INVALID_EXTERNAL_HISTORY_SEMANTICS = 8,
    /*
     * The user-supplied restart persistence counter failed
     * to produce the next sequence id.
     */
    MODALITY_PROBE_ERROR_RESTART_PERSISTENCE_SEQUENCE_ID_UNAVAILABLE = 9,
    /*
     * A wall clock time outside of the allowed range was provided.
     */
    MODALITY_PROBE_ERROR_INVALID_WALL_CLOCK_TIME = 10,
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
 * Modality probe severity level specifying macro.
 *
 * This is a no-op macro used to expose metadata to the CLI tooling.
 *
 * The levels are aligned with the FMEA severity ratings, going
 * from one to ten, with one indicating negligible or nonexistent harm,
 * and ten indicating a safety or regulatory hazard.
 *
 * Example use:
 * ```c
 * MODALITY_SEVERITY(1)
 * ```
 *
 */
#define MODALITY_SEVERITY(level)

/*
 * Modality probe instance initializer macro.
 *
 * Used to expose probe information to the CLI tooling.
 *
 * Expands to call:
 * `modality_probe_initialize(dest, dest_size, probe_id, time_resolution, wall_clock_id, next_sid_fn, next_sid_state, probe)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the probe description
 *
 */
#define MODALITY_PROBE_INIT(dest, dest_size, probe_id, time_res, wc_id, next_sid_fn, next_sid_state, probe, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_initialize(dest, dest_size, probe_id, time_res, wc_id, next_sid_fn, next_sid_state, probe) : MODALITY_PROBE_ERROR_OK)

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
 * Modality probe event recording with time macro.
 *
 * Used to expose event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record_event_with_time(probe, event, time_ns)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - A string for the event description
 *
 */
#define MODALITY_PROBE_RECORD_W_TIME(probe, event, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_time(\
            probe, \
            event, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

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
 * Event with payload descriptions may additionally use a single
 * format specifier token (`{}`) to have the payload value formatted
 * in the description when displayed.
 *
 */
#define MODALITY_PROBE_RECORD_W_I8(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i8(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_I8_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i8_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_U8(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u8(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U8_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u8_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_I16(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i16(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_I16_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i16_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_U16(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u16(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U16_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u16_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_I32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_I32_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_i32_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_U32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_U32_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u32_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_BOOL(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_bool(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_BOOL_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_bool_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

#define MODALITY_PROBE_RECORD_W_F32(probe, event, payload, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_f32(\
            probe, \
            event, \
            payload) : MODALITY_PROBE_ERROR_OK)
#define MODALITY_PROBE_RECORD_W_F32_W_TIME(probe, event, payload, time_ns, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_f32_with_time(\
            probe, \
            event, \
            payload, \
            time_ns) : MODALITY_PROBE_ERROR_OK)

/*
 * Modality probe expectation expression event recording macro.
 *
 * Used to expose expectation event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record_event_with_payload_u32(probe, event, expression_outcome)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - Severity level: MODALITY_SEVERITY(<level>)
 * - A string for the event description
 *
 * Event with payload descriptions may additionally use a single
 * format specifier token (`{}`) to have the payload value formatted
 * in the description when displayed.
 *
 */
#define MODALITY_PROBE_EXPECT(probe, event, expr, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event_with_payload_u32(\
            probe, \
            event, \
            (expr)) : MODALITY_PROBE_ERROR_OK)

/*
 * Modality probe failure event recording macro.
 *
 * Used to expose failure event recording information to the CLI tooling.
 *
 * Expands to call `modality_probe_record(probe, event)`.
 *
 * The trailing variadic macro arguments accept (in any order):
 * - Tags: MODALITY_TAGS(<tag>[,<tag>])
 * - Severity level: MODALITY_SEVERITY(<level>)
 * - A string for the event description
 *
 */
#define MODALITY_PROBE_FAILURE(probe, event, ...) \
    ((MODALITY_PROBE_MACROS_ENABLED) ? modality_probe_record_event(\
            probe, \
            event) : MODALITY_PROBE_ERROR_OK)

/*
 * Create a Modality probe instance. probe_id must be non-zero.
 *
 * If next_sequence_id_fn is null, then next_sequence_id_user_state
 * is unused and this probe will not do any restart handling
 * (any events logged after a restart will be seen as duplicates).
 *
 * Otherwise, if next_sequence_id_fn is non-null, then the probe
 * will call this function to retrieve a new sequence number when
 * needed.
 */
size_t modality_probe_initialize(
        uint8_t *destination,
        size_t destination_size_bytes,
        uint32_t probe_id,
        uint32_t time_resolution_ns,
        uint16_t wall_clock_id,
        modality_probe_next_sequence_id_fn next_sequence_id_fn,
        void *next_sequence_id_user_state,
        modality_probe **out);

/*
 * Record time.
 */
size_t modality_probe_record_time(
        modality_probe *probe,
        uint64_t time_ns);

/*
 * Record an event.
 * event_id must be non-zero.
 */
size_t modality_probe_record_event(
        modality_probe *probe,
        uint32_t event_id);

/*
 * Record an event.
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_time(
        modality_probe *probe,
        uint32_t event_id,
        uint64_t time_ns);

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
 * Record an event along with a 4-byte payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_with_time(
        modality_probe *probe,
        uint32_t event_id,
        uint32_t payload,
        uint64_t time_ns);

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
 * Record an event along with a i8 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i8_with_time(
        modality_probe *probe,
        uint32_t event_id,
        int8_t payload,
        uint64_t time_ns);

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
 * Record an event along with a u8 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u8_with_time(
        modality_probe *probe,
        uint32_t event_id,
        uint8_t payload,
        uint64_t time_ns);

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
 * Record an event along with a i16 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i16_with_time(
        modality_probe *probe,
        uint32_t event_id,
        int16_t payload,
        uint64_t time_ns);

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
 * Record an event along with a u16 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u16_with_time(
        modality_probe *probe,
        uint32_t event_id,
        uint16_t payload,
        uint64_t time_ns);

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
 * Record an event along with a i32 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_i32_with_time(
        modality_probe *probe,
        uint32_t event_id,
        int32_t payload,
        uint64_t time_ns);

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
 * Record an event along with a u32 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_u32_with_time(
        modality_probe *probe,
        uint32_t event_id,
        uint32_t payload,
        uint64_t time_ns);

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
 * Record an event along with a bool payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_bool_with_time(
        modality_probe *probe,
        uint32_t event_id,
        bool payload,
        uint64_t time_ns);

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
 * Record an event along with a f32 payload and time.
 *
 * event_id must be non-zero.
 */
size_t modality_probe_record_event_with_payload_f32_with_time(
        modality_probe *probe,
        uint32_t event_id,
        float payload,
        uint64_t time_ns);

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
        modality_probe_causal_snapshot *snapshot);

/*
 * Produce a transmittable summary of this Modality probe's
 * causal history and time for use by another Modality probe elsewhere
 * in the system.
 */
size_t modality_probe_produce_snapshot_with_time(
        modality_probe *probe,
        uint64_t time_ns,
        modality_probe_causal_snapshot *snapshot);

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
 * Produce a transmittable opaque blob of this Modality probe's
 * causal history and time for use by another Modality probe elsewhere
 * in the system.
 *
 * Populates the number of bytes written in out_written_bytes.
 */
size_t modality_probe_produce_snapshot_bytes_with_time(
        modality_probe *probe,
        uint64_t time_ns,
        uint8_t *history_destination,
        size_t history_destination_bytes,
        size_t *out_written_bytes);

/*
 * Consume a causal history summary structure provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot(
        modality_probe *probe,
        const modality_probe_causal_snapshot *snapshot);

/*
 * Consume a causal history summary structure with time provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot_with_time(
        modality_probe *probe,
        const modality_probe_causal_snapshot *snapshot,
        uint64_t time_ns);

/*
 * Consume a opaque causal history blob provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot_bytes(
        modality_probe *probe,
        const uint8_t *history_source,
        size_t history_source_bytes);

/*
 * Consume a opaque causal history blob with time provided
 * by some other Modality probe.
 */
size_t modality_probe_merge_snapshot_bytes_with_time(
        modality_probe *probe,
        const uint8_t *history_source,
        size_t history_source_bytes,
        uint64_t time_ns);

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

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* MODALITY_PROBE_H */
