/// Convenience macro that calls
/// [Ekotrace::record_event](struct.Ekotrace.html#method.record_event).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export]
macro_rules! ekt_record {
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
macro_rules! ekt_try_record {
    ($tracer:expr, $event:expr) => {
        $tracer.try_record_event($event)
    };
    ($tracer:expr, $event:expr, $desc:tt) => {
        $tracer.try_record_event($event)
    };
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_i8 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_u8 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_i16 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_u16 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_i32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_u32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_bool {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_metadata](struct.Ekotrace.html#method.record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_record_w_f32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_i8 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_u8 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_i16 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_u16 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_i32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_u32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_bool {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_metadata](struct.Ekotrace.html#method.try_record_event_with_metadata).
///
/// The optional description string argument compiles away, and is
/// used only by the CLI tooling.
#[macro_export(local_inner_macros)]
macro_rules! ekt_try_record_w_f32 {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __try_record_with!($tracer, $event, $meta)
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __try_record_with!($tracer, $event, $meta, $desc)
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __record_with {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __meta_as_u32_impls!();
        $tracer.record_event_with_metadata($event, $meta.as_u32())
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __meta_as_u32_impls!();
        $tracer.record_event_with_metadata($event, $meta.as_u32())
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __try_record_with {
    ($tracer:expr, $event:expr, $meta:expr) => {{
        __meta_as_u32_impls!();
        $tracer.try_record_event_with_metadata($event, $meta.as_u32())
    }};
    ($tracer:expr, $event:expr, $meta:expr, $desc:tt) => {{
        __meta_as_u32_impls!();
        $tracer.try_record_event_with_metadata($event, $meta.as_u32())
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __meta_as_u32_impls {
    () => {
        trait MetaAsU32 {
            fn as_u32(&self) -> u32;
        }
        impl MetaAsU32 for i8 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for u8 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for i16 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for u16 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for i32 {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for u32 {
            fn as_u32(&self) -> u32 {
                *self
            }
        }
        impl MetaAsU32 for bool {
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
        impl MetaAsU32 for f32 {
            fn as_u32(&self) -> u32 {
                u32::from_le_bytes(self.to_le_bytes())
            }
        }
    };
}
