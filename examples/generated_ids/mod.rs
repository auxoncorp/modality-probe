/*
 * GENERATED CODE, DO NOT EDIT
 *
 * Component:
 *   Name: component
 *   ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
 *   Code hash: 48cb2ddc0e262f757a49b341cca993846254f1901301ee51e53929a40eae5a0f
 *   Instrumentation hash: c0f8f7124d187e95b336424b2be23678e984b7216a0582da5cb0c0b2c46093e4
 */

/*
 * Probes (sha3-256 27b1b2bce4a996897ee49aaba8b5ab90b0b7840292841cd3d1596070d00e06e0)
 */

/// Name: PROBE_ID_FOO
/// Description: Example probe
/// Component ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
/// Tags: example
/// Location: examples/event-recording.rs:27
pub const PROBE_ID_FOO: u32 = 177606824;

/*
 * Events (sha3-256 bbfee146dc21c1827e49e1bcd2e8ca6a03fe755b982112a157c25afc95a21c93)
 */

/// Name: TOP_OF_THE_LOOP
/// Description: At the top of the loop
/// Component ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
/// Tags: example;my-tag
/// Payload type:
/// Location: examples/event-recording.rs:38
pub const TOP_OF_THE_LOOP: u32 = 1;

/// Name: MOD10_CONDITION_EVENT
/// Description: Loop counter % 10 event
/// Component ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
/// Tags: EXPECTATION;example
/// Payload type: u32
/// Location: examples/event-recording.rs:46
pub const MOD10_CONDITION_EVENT: u32 = 2;

/// Name: LOOP_COUNTER_EVENT
/// Description: Loop counter event happened
/// Component ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
/// Tags:
/// Payload type:
/// Location: examples/event-recording.rs:56
pub const LOOP_COUNTER_EVENT: u32 = 3;

/// Name: REPORT_CREATED
/// Description: Report created
/// Component ID: cae8cd33-26c6-4c33-acd4-84e3a1b84b58
/// Tags: another tag
/// Payload type: u32
/// Location: examples/event-recording.rs:71
pub const REPORT_CREATED: u32 = 4;
