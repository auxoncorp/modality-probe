/// Convenience macro that calls
/// [Ekotrace::record_event](struct.Ekotrace.html#method.record_event).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export]
macro_rules! record {
    ($tracer:expr, $event:expr) => {
        $tracer.record_event($event)
    };
    ($tracer:expr, $event:expr, $desc:tt) => {
        $tracer.record_event($event)
    };
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event](struct.Ekotrace.html#method.try_record_event).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export]
macro_rules! try_record {
    ($tracer:expr, $event:expr) => {
        $tracer.try_record_event($event)
    };
    ($tracer:expr, $event:expr, $desc:tt) => {
        $tracer.try_record_event($event)
    };
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_i8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_u8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_i16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_u16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_i32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_u32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_bool {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! record_w_f32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_bool {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_f32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $payload, $desc)
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __record_with {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __payload_as_u32_impls!();
        $tracer.record_event_with_payload($event, $payload.as_u32())
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __payload_as_u32_impls!();
        $tracer.record_event_with_payload($event, $payload.as_u32())
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __try_record_with {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __payload_as_u32_impls!();
        $tracer.try_record_event_with_payload($event, $payload.as_u32())
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc:tt) => {{
        __payload_as_u32_impls!();
        $tracer.try_record_event_with_payload($event, $payload.as_u32())
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __payload_as_u32_impls {
    () => {
        trait PayloadAsU32 {
            fn as_u32(&self) -> u32;
        }
        impl PayloadAsU32 for i8 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for u8 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for i16 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for u16 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for i32 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for u32 {
            fn as_u32(&self) -> u32 {
                *self
            }
        }
        impl PayloadAsU32 for bool {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl PayloadAsU32 for f32 {
            fn as_u32(&self) -> u32 {
                self.to_bits()
            }
        }
    };
}
