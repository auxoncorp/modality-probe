/// Convenience macro that calls
/// [Ekotrace::initialize_at](struct.Ekotrace.html#method.initialize_at).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! initialize_at {
    ($storage:expr, $tracer_id:expr) => {
        Ekotrace::initialize_at($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt) => {
        Ekotrace::initialize_at($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        Ekotrace::initialize_at($storage, $tracer_id)
    };
}

/// Convenience macro that calls
/// [Ekotrace::try_initialize_at](struct.Ekotrace.html#method.try_initialize_at).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! try_initialize_at {
    ($storage:expr, $tracer_id:expr) => {
        Ekotrace::try_initialize_at($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt) => {
        Ekotrace::try_initialize_at($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        Ekotrace::try_initialize_at($storage, $tracer_id)
    };
}

/// Convenience macro that calls
/// [Ekotrace::new_with_storage](struct.Ekotrace.html#method.new_with_storage).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! new_with_storage {
    ($storage:expr, $tracer_id:expr) => {
        Ekotrace::new_with_storage($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt) => {
        Ekotrace::new_with_storage($storage, $tracer_id)
    };
    ($storage:expr, $tracer_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        Ekotrace::new_with_storage($storage, $tracer_id)
    };
}

/// Convenience macro that calls
/// [Ekotrace::record_event](struct.Ekotrace.html#method.record_event).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! record {
    ($tracer:expr, $event:expr) => {
        $tracer.record_event($event)
    };
    ($tracer:expr, $event:expr, $desc_or_tags:tt) => {
        $tracer.record_event($event)
    };
    ($tracer:expr, $event:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        $tracer.record_event($event)
    };
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event](struct.Ekotrace.html#method.try_record_event).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! try_record {
    ($tracer:expr, $event:expr) => {
        $tracer.try_record_event($event)
    };
    ($tracer:expr, $event:expr, $desc_or_tags:tt) => {
        $tracer.try_record_event($event)
    };
    ($tracer:expr, $event:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        $tracer.try_record_event($event)
    };
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_bool {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::record_event_with_payload](struct.Ekotrace.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_f32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u8 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u16 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_bool {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [Ekotrace::try_record_event_with_payload](struct.Ekotrace.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_f32 {
    ($tracer:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
    ($tracer:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($tracer, $event, $payload)
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __record_with {
    ($tracer:expr, $event:expr, $payload:expr) => {{
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

#[cfg(test)]
mod tests {
    use crate::{Ekotrace, EventId, Tracer, TracerId};

    #[test]
    fn event_macro_use() {
        let tracer_id = TracerId::new(1).unwrap();
        let mut storage = [0_u8; 1024];
        let tracer = Ekotrace::initialize_at(&mut storage, tracer_id).unwrap();
        const EVENT_D: u32 = 1;
        record!(tracer, EventId::new(EVENT_D).unwrap());
        record!(tracer, EventId::new(EVENT_D).unwrap(), "desc");
        record!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            "tags=some-tag",
            "desc"
        );

        record_w_i8!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_u8!(tracer, EventId::new(EVENT_D).unwrap(), 0);
        record_w_i16!(tracer, EventId::new(EVENT_D).unwrap(), 0, "desc");
        record_w_u16!(tracer, EventId::new(EVENT_D).unwrap(), 0, "tags=some-tag");
        record_w_i32!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_u32!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_bool!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            true,
            "tags=some-tag",
            "desc"
        );
        record_w_f32!(
            tracer,
            EventId::new(EVENT_D).unwrap(),
            0.0,
            "tags=some-tag",
            "desc"
        );

        try_record!(tracer, EVENT_D).unwrap();
        try_record!(tracer, EVENT_D, "desc").unwrap();
        try_record!(tracer, EVENT_D, "tags=some-tag", "desc").unwrap();

        try_record_w_i8!(tracer, EVENT_D, 0).unwrap();
        try_record_w_u8!(tracer, EVENT_D, 0, "desc").unwrap();
        try_record_w_i16!(tracer, EVENT_D, 0, "tags=some-tag").unwrap();
        try_record_w_u16!(tracer, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_i32!(tracer, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_u32!(tracer, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_bool!(tracer, EVENT_D, false, "tags=some-tag", "desc").unwrap();
        try_record_w_f32!(tracer, EVENT_D, 0.0, "tags=some-tag", "desc").unwrap();
    }

    #[test]
    fn tracer_macro_use() {
        let tracer_id = TracerId::new(1).unwrap();
        let mut storage = [0_u8; 1024];
        let _tracer = initialize_at!(&mut storage, tracer_id).unwrap();
        let _tracer = initialize_at!(&mut storage, tracer_id, "desc").unwrap();
        let _tracer = initialize_at!(&mut storage, tracer_id, "desc", "tags=some-tag").unwrap();
        let _tracer = try_initialize_at!(&mut storage, 1).unwrap();
        let _tracer = try_initialize_at!(&mut storage, 1, "tags=some-tag").unwrap();
        let _tracer = try_initialize_at!(&mut storage, 1, "tags=some-tag", "desc").unwrap();
        let _tracer = new_with_storage!(&mut storage, tracer_id).unwrap();
        let _tracer = new_with_storage!(&mut storage, tracer_id, "desc").unwrap();
        let _tracer = new_with_storage!(&mut storage, tracer_id, "tags=some-tag", "desc").unwrap();
    }
}
