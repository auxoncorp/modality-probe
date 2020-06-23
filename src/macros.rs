/// Convenience macro that calls
/// [ModalityProbe::initialize_at](struct.ModalityProbe.html#method.initialize_at).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! initialize_at {
    ($storage:expr, $probe_id:expr) => {
        ModalityProbe::initialize_at($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt) => {
        ModalityProbe::initialize_at($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        ModalityProbe::initialize_at($storage, $probe_id)
    };
}

/// Convenience macro that calls
/// [ModalityProbe::try_initialize_at](struct.ModalityProbe.html#method.try_initialize_at).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! try_initialize_at {
    ($storage:expr, $probe_id:expr) => {
        ModalityProbe::try_initialize_at($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt) => {
        ModalityProbe::try_initialize_at($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        ModalityProbe::try_initialize_at($storage, $probe_id)
    };
}

/// Convenience macro that calls
/// [ModalityProbe::new_with_storage](struct.ModalityProbe.html#method.new_with_storage).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! new_with_storage {
    ($storage:expr, $probe_id:expr) => {
        ModalityProbe::new_with_storage($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt) => {
        ModalityProbe::new_with_storage($storage, $probe_id)
    };
    ($storage:expr, $probe_id:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        ModalityProbe::new_with_storage($storage, $probe_id)
    };
}

/// Convenience macro that calls
/// [ModalityProbe::record_event](struct.ModalityProbe.html#method.record_event).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! record {
    ($probe:expr, $event:expr) => {
        $probe.record_event($event)
    };
    ($probe:expr, $event:expr, $desc_or_tags:tt) => {
        $probe.record_event($event)
    };
    ($probe:expr, $event:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        $probe.record_event($event)
    };
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event](struct.ModalityProbe.html#method.try_record_event).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export]
macro_rules! try_record {
    ($probe:expr, $event:expr) => {
        $probe.try_record_event($event)
    };
    ($probe:expr, $event:expr, $desc_or_tags:tt) => {
        $probe.try_record_event($event)
    };
    ($probe:expr, $event:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {
        $probe.try_record_event($event)
    };
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i8 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u8 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i16 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u16 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_i32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_u32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_bool {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! record_w_f32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i8 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u8 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i16 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u16 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_i32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_u32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_bool {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_record_w_f32 {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
    ($probe:expr, $event:expr, $payload:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $payload)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::record_event_with_payload](struct.ModalityProbe.html#method.record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! expect {
    ($probe:expr, $event:expr, $expression:expr) => {{
        __record_with!($probe, $event, $expression)
    }};
    ($probe:expr, $event:expr, $expression:expr, $desc_or_tags:tt) => {{
        __record_with!($probe, $event, $expression)
    }};
    ($probe:expr, $event:expr, $expression:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __record_with!($probe, $event, $expression)
    }};
}

/// Convenience macro that calls
/// [ModalityProbe::try_record_event_with_payload](struct.ModalityProbe.html#method.try_record_event_with_payload).
///
/// The optional description and tags string arguments are only used
/// by the CLI and compile away.
///
/// The format for the tags string is: `"tags=<tag>[;<tag>]"`
#[macro_export(local_inner_macros)]
macro_rules! try_expect {
    ($probe:expr, $event:expr, $expression:expr) => {{
        __try_record_with!($probe, $event, $expression)
    }};
    ($probe:expr, $event:expr, $expression:expr, $desc_or_tags:tt) => {{
        __try_record_with!($probe, $event, $expression)
    }};
    ($probe:expr, $event:expr, $expression:expr, $desc_or_tags:tt, $tags_or_desc:tt) => {{
        __try_record_with!($probe, $event, $expression)
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __record_with {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __payload_as_u32_impls!();
        $probe.record_event_with_payload($event, $payload.as_u32())
    }};
}

#[doc(hidden)]
#[macro_export(local_inner_macros)]
macro_rules! __try_record_with {
    ($probe:expr, $event:expr, $payload:expr) => {{
        __payload_as_u32_impls!();
        $probe.try_record_event_with_payload($event, $payload.as_u32())
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
    use crate::{EventId, ModalityProbe, Probe, ProbeId};

    #[test]
    fn event_macro_use() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut storage = [0_u8; 1024];
        let probe = ModalityProbe::initialize_at(&mut storage, probe_id).unwrap();
        const EVENT_D: u32 = 1;
        record!(probe, EventId::new(EVENT_D).unwrap());
        record!(probe, EventId::new(EVENT_D).unwrap(), "desc");
        record!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            "tags=some-tag",
            "desc"
        );

        record_w_i8!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_u8!(probe, EventId::new(EVENT_D).unwrap(), 0);
        record_w_i16!(probe, EventId::new(EVENT_D).unwrap(), 0, "desc");
        record_w_u16!(probe, EventId::new(EVENT_D).unwrap(), 0, "tags=some-tag");
        record_w_i32!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_u32!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            0,
            "tags=some-tag",
            "desc"
        );
        record_w_bool!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            true,
            "tags=some-tag",
            "desc"
        );
        record_w_f32!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            0.0,
            "tags=some-tag",
            "desc"
        );

        try_record!(probe, EVENT_D).unwrap();
        try_record!(probe, EVENT_D, "desc").unwrap();
        try_record!(probe, EVENT_D, "tags=some-tag", "desc").unwrap();

        try_record_w_i8!(probe, EVENT_D, 0).unwrap();
        try_record_w_u8!(probe, EVENT_D, 0, "desc").unwrap();
        try_record_w_i16!(probe, EVENT_D, 0, "tags=some-tag").unwrap();
        try_record_w_u16!(probe, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_i32!(probe, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_u32!(probe, EVENT_D, 0, "tags=some-tag", "desc").unwrap();
        try_record_w_bool!(probe, EVENT_D, false, "tags=some-tag", "desc").unwrap();
        try_record_w_f32!(probe, EVENT_D, 0.0, "tags=some-tag", "desc").unwrap();

        expect!(probe, EventId::new(EVENT_D).unwrap(), 1 == 0);
        expect!(probe, EventId::new(EVENT_D).unwrap(), 1_i8 == 0_i8, "desc");
        expect!(
            probe,
            EventId::new(EVENT_D).unwrap(),
            "s1" != "s2",
            "tags=severity.1",
            "desc"
        );

        try_expect!(probe, EVENT_D, true == true).unwrap();
        try_expect!(probe, EVENT_D, 1 == (2 - 1), "desc").unwrap();
        let a = 1;
        let b = 2;
        try_expect!(probe, EVENT_D, a != b, "desc", "tags=my expectation").unwrap();
    }

    #[test]
    fn probe_macro_use() {
        let probe_id = ProbeId::new(1).unwrap();
        let mut storage = [0_u8; 1024];
        let _probe = initialize_at!(&mut storage, probe_id).unwrap();
        let _probe = initialize_at!(&mut storage, probe_id, "desc").unwrap();
        let _probe = initialize_at!(&mut storage, probe_id, "desc", "tags=some-tag").unwrap();
        let _probe = try_initialize_at!(&mut storage, 1).unwrap();
        let _probe = try_initialize_at!(&mut storage, 1, "tags=some-tag").unwrap();
        let _probe = try_initialize_at!(&mut storage, 1, "tags=some-tag", "desc").unwrap();
        let _probe = new_with_storage!(&mut storage, probe_id).unwrap();
        let _probe = new_with_storage!(&mut storage, probe_id, "desc").unwrap();
        let _probe = new_with_storage!(&mut storage, probe_id, "tags=some-tag", "desc").unwrap();
    }
}
