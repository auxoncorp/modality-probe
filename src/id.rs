//! Identifiers critical to the Ekotrace system
use crate::{InvalidEventId, InvalidTracerId};
use core::convert::{TryFrom, TryInto};
use core::num::NonZeroU32;

/// Ought to uniquely identify a location for where events occur within a system under test.
///
/// Typically represents a single thread.
///
/// Must be backed by a value greater than 0 and less than or equal to
/// TracerId::MAX_ID.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
pub struct TracerId(
    /* Never make this inner field truly public */ pub(crate) NonZeroU32,
);

impl TracerId {
    /// The largest permissible backing id value
    pub const MAX_ID: u32 = 0b0011_1111_1111_1111_1111_1111_1111_1111;

    /// raw_id must be greater than 0 and less than 0b1000_0000_0000_0000_0000_0000_0000_0000
    #[inline]
    pub fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_ID {
            return None;
        }
        NonZeroU32::new(raw_id).map(Self)
    }

    /// Get the underlying value with Rust's assurances
    /// of non-zero-ness.
    #[inline]
    pub fn get(self) -> NonZeroU32 {
        self.0
    }

    /// Get the underlying value as a convenient primitive
    #[inline]
    pub fn get_raw(self) -> u32 {
        self.0.get()
    }
}

impl From<TracerId> for NonZeroU32 {
    #[inline]
    fn from(t: TracerId) -> Self {
        t.0
    }
}

impl From<TracerId> for u32 {
    #[inline]
    fn from(t: TracerId) -> Self {
        t.0.get()
    }
}

macro_rules! infallible_sizing_try_from_impl {
    ($prim_ty:ty, $target_ty:ty, $err_ty:ty, $err_constructor:expr) => {
        impl TryFrom<$prim_ty> for $target_ty {
            type Error = $err_ty;
            #[inline]
            fn try_from(raw_id: $prim_ty) -> Result<Self, Self::Error> {
                match <$target_ty>::new(raw_id.into()) {
                    Some(id) => Ok(id),
                    None => Err($err_constructor),
                }
            }
        }
    };
}

macro_rules! fallible_sizing_try_from_impl {
    ($prim_ty:ty, $target_ty:ty, $err_ty:ty, $err_constructor:expr) => {
        impl TryFrom<$prim_ty> for $target_ty {
            type Error = $err_ty;
            #[inline]
            fn try_from(raw_id: $prim_ty) -> Result<Self, Self::Error> {
                let intermediate_id: u32 = match raw_id.try_into() {
                    Ok(i) => i,
                    Err(_) => return Err($err_constructor),
                };
                match <$target_ty>::new(intermediate_id) {
                    Some(id) => Ok(id),
                    None => Err($err_constructor),
                }
            }
        }
    };
}

macro_rules! infallible_sizing_try_from_impl_with_internal {
    ($prim_ty:ty, $target_ty:ty, $err_ty:ty, $err_constructor:expr) => {
        impl TryFrom<$prim_ty> for $target_ty {
            type Error = $err_ty;
            #[inline]
            fn try_from(raw_id: $prim_ty) -> Result<Self, Self::Error> {
                match <$target_ty>::new(raw_id.into()) {
                    Some(id) => Ok(id),
                    None => match <$target_ty>::new_internal(raw_id.into()) {
                        Some(id) => Ok(id),
                        None => Err($err_constructor),
                    },
                }
            }
        }
    };
}

macro_rules! fallible_sizing_try_from_impl_with_internal {
    ($prim_ty:ty, $target_ty:ty, $err_ty:ty, $err_constructor:expr) => {
        impl TryFrom<$prim_ty> for $target_ty {
            type Error = $err_ty;
            #[inline]
            fn try_from(raw_id: $prim_ty) -> Result<Self, Self::Error> {
                let intermediate_id: u32 = match raw_id.try_into() {
                    Ok(i) => i,
                    Err(_) => return Err($err_constructor),
                };
                match <$target_ty>::new(intermediate_id) {
                    Some(id) => Ok(id),
                    None => match <$target_ty>::new_internal(intermediate_id) {
                        Some(id) => Ok(id),
                        None => Err($err_constructor),
                    },
                }
            }
        }
    };
}

infallible_sizing_try_from_impl!(u8, TracerId, InvalidTracerId, InvalidTracerId);
infallible_sizing_try_from_impl!(u16, TracerId, InvalidTracerId, InvalidTracerId);
infallible_sizing_try_from_impl!(u32, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(u64, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(u128, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(usize, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(i8, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(i16, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(i32, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(i64, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(i128, TracerId, InvalidTracerId, InvalidTracerId);
fallible_sizing_try_from_impl!(isize, TracerId, InvalidTracerId, InvalidTracerId);

infallible_sizing_try_from_impl_with_internal!(u8, EventId, InvalidEventId, InvalidEventId);
infallible_sizing_try_from_impl_with_internal!(u16, EventId, InvalidEventId, InvalidEventId);
infallible_sizing_try_from_impl_with_internal!(u32, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(u64, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(u128, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(usize, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(i8, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(i16, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(i32, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(i64, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(i128, EventId, InvalidEventId, InvalidEventId);
fallible_sizing_try_from_impl_with_internal!(isize, EventId, InvalidEventId, InvalidEventId);

/// Uniquely identify an event or kind of event.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
#[repr(transparent)]
pub struct EventId(NonZeroU32);

impl EventId {
    /// The maximum permissible id value for an Event at all
    ///
    /// This value is different from MAX_USER_ID in order to
    /// support a reserved range of EventIds for protocol use
    pub const MAX_INTERNAL_ID: u32 = 0b0011_1111_1111_1111_1111_1111_1111_1111;
    /// The number of id values that are reserved for use by the
    /// tracer implementation.
    pub const NUM_RESERVED_IDS: u32 = 256;
    /// The maximum-permissible id value for for an Event
    /// defined by end users.
    pub const MAX_USER_ID: u32 = EventId::MAX_INTERNAL_ID - EventId::NUM_RESERVED_IDS;

    /// The tracer produced a log report for transmission to the backend
    /// for external analysis.
    pub const EVENT_PRODUCED_EXTERNAL_REPORT: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 1) });
    /// There was not sufficient room in memory to store all desired events or clock data
    pub const EVENT_LOG_OVERFLOWED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 2) });
    /// A logical clock's count reached the maximum trackable value
    pub const EVENT_LOGICAL_CLOCK_OVERFLOWED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 3) });
    /// The local tracing instance (e.g. Ekotrace) did not have enough memory
    /// reserved to store enough logical clocks to track all of the unique
    /// neighbors that attempt to communicate with it.
    pub const EVENT_NUM_CLOCKS_OVERFLOWED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 4) });

    /// The events reserved for internal use
    pub const INTERNAL_EVENTS: &'static [EventId] = &[
        EventId::EVENT_PRODUCED_EXTERNAL_REPORT,
        EventId::EVENT_LOG_OVERFLOWED,
        EventId::EVENT_LOGICAL_CLOCK_OVERFLOWED,
        EventId::EVENT_NUM_CLOCKS_OVERFLOWED,
    ];

    /// raw_id must be greater than 0 and less than EventId::MAX_USER_ID
    #[inline]
    pub fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_USER_ID {
            return None;
        }
        NonZeroU32::new(raw_id).map(Self)
    }

    /// A means of generating ids for internal protocol use.
    /// raw_id must be greater than EventId::MAX_USER_ID and
    /// less than or equal to EventId::MAX_INTERNAL_ID
    #[inline]
    pub fn new_internal(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_USER_ID && raw_id <= Self::MAX_INTERNAL_ID {
            NonZeroU32::new(raw_id).map(Self)
        } else {
            None
        }
    }

    /// Get the underlying value with Rust's assurances
    /// of non-zero-ness.
    #[inline]
    pub fn get(self) -> NonZeroU32 {
        self.0
    }

    /// Get the underlying value as a convenient primitive
    #[inline]
    pub fn get_raw(self) -> u32 {
        self.0.get()
    }

    /// Is this id part of the set of IDs reserved for internal
    /// protocol use?
    #[inline]
    pub fn is_internal(self) -> bool {
        self.get_raw() > Self::MAX_USER_ID && self.get_raw() <= Self::MAX_INTERNAL_ID
    }
}

impl From<EventId> for NonZeroU32 {
    #[inline]
    fn from(e: EventId) -> Self {
        e.0
    }
}

impl From<EventId> for u32 {
    #[inline]
    fn from(e: EventId) -> Self {
        e.0.get()
    }
}

/// This module contains a proptest `Arbitrary` implementation for
/// event ids. It is only present if the `"std"` feature is set.
#[cfg(feature = "std")]
pub mod prop {
    use proptest::{
        num::u32::BinarySearch,
        prelude::{Arbitrary, RngCore},
        strategy::{NewTree, Strategy, ValueTree},
        test_runner::TestRunner,
    };

    use super::*;

    /// A proptest value tree for event ids. It builds off of u32's
    /// binary search and clamps on valid _user_ values.
    pub struct EventIdBinarySearch(BinarySearch);

    impl EventIdBinarySearch {
        fn or_max(x: u32) -> EventId {
            let x1 = x.checked_add(1).unwrap_or_else(|| EventId::MAX_USER_ID);
            if x1 > EventId::MAX_USER_ID {
                return EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_USER_ID) });
            }
            EventId(unsafe { NonZeroU32::new_unchecked(x1) })
        }
    }

    impl ValueTree for EventIdBinarySearch {
        type Value = EventId;

        fn current(&self) -> EventId {
            EventIdBinarySearch::or_max(self.0.current())
        }

        fn simplify(&mut self) -> bool {
            self.0.simplify()
        }

        fn complicate(&mut self) -> bool {
            self.0.complicate()
        }
    }

    #[derive(Debug)]
    /// A proptest strategy to be used for any valid user event id.
    pub struct AnyEventId;

    impl Strategy for AnyEventId {
        type Tree = EventIdBinarySearch;
        type Value = EventId;

        fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
            Ok(EventIdBinarySearch(BinarySearch::new(
                runner.rng().next_u32().saturating_add(1),
            )))
        }
    }

    impl Arbitrary for EventId {
        type Parameters = ();
        type Strategy = AnyEventId;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            AnyEventId
        }
    }

    /// A proptest value tree for tracer ids. It builds off of u32's
    /// binary search.
    pub struct TracerIdBinarySearch(BinarySearch);

    impl TracerIdBinarySearch {
        fn or_max(x: u32) -> TracerId {
            let x1: u32 = x.checked_add(1).unwrap_or_else(|| core::u32::MAX);
            TracerId(unsafe { NonZeroU32::new_unchecked(x1) })
        }
    }

    impl ValueTree for TracerIdBinarySearch {
        type Value = TracerId;

        fn current(&self) -> TracerId {
            TracerIdBinarySearch::or_max(self.0.current())
        }

        fn simplify(&mut self) -> bool {
            self.0.simplify()
        }

        fn complicate(&mut self) -> bool {
            self.0.complicate()
        }
    }

    #[derive(Debug)]
    /// A proptest strategy to be used for any valid tracer id.
    pub struct AnyTracerId;

    impl Strategy for AnyTracerId {
        type Tree = TracerIdBinarySearch;
        type Value = TracerId;

        fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
            Ok(TracerIdBinarySearch(BinarySearch::new(
                runner.rng().next_u32().saturating_add(1),
            )))
        }
    }

    impl Arbitrary for TracerId {
        type Parameters = ();
        type Strategy = AnyTracerId;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            AnyTracerId
        }
    }
}

#[cfg(feature = "std")]
pub use prop::*;

#[cfg(test)]
pub(crate) mod id_tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn new_ids_cannot_have_zero_values() {
        assert!(TracerId::new(0).is_none());
        assert!(EventId::new(0).is_none());
        assert!(EventId::new_internal(0).is_none());
    }

    #[test]
    fn boundary_values() {
        assert!(TracerId::new(TracerId::MAX_ID).is_some());
        assert!(EventId::new(EventId::MAX_USER_ID).is_some());
        assert!(EventId::new_internal(EventId::MAX_INTERNAL_ID).is_some());

        assert!(EventId::new_internal(EventId::MAX_USER_ID).is_none());
        assert!(EventId::new(EventId::MAX_INTERNAL_ID).is_none());
    }

    prop_compose! {
        pub(crate) fn gen_raw_tracer_id()(raw_id in 1..=TracerId::MAX_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub(crate) fn gen_tracer_id()(raw_id in 1..=TracerId::MAX_ID) -> TracerId {
            raw_id.try_into().unwrap()
        }
    }

    prop_compose! {
        fn gen_raw_invalid_tracer_id()(raw_id in (TracerId::MAX_ID+1)..core::u32::MAX) -> u32 {
            raw_id
        }
    }

    proptest! {
        #[test]
        fn valid_tracer_ids_are_accepted(raw_id in gen_raw_tracer_id()) {
            let t = TracerId::new(raw_id).unwrap();
            assert_eq!(t.get_raw(), raw_id);
        }

        #[test]
        fn invalid_tracer_ids_are_rejected(raw_id in gen_raw_invalid_tracer_id()) {
            assert_eq!(None, TracerId::new(raw_id));
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_internal_event_id()(raw_id in (EventId::MAX_USER_ID + 1)..EventId::MAX_INTERNAL_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub(crate) fn gen_raw_user_event_id()(raw_id in 1..=EventId::MAX_USER_ID) -> u32 {
            raw_id
        }
    }
    prop_compose! {
        fn gen_raw_invalid_event_id()(raw_id in (EventId::MAX_INTERNAL_ID+1)..core::u32::MAX) -> u32 {
            raw_id
        }
    }

    proptest! {
        #[test]
        fn user_event_ids_are_allowed_via_regular_new_constructor(raw_id in gen_raw_user_event_id()) {
            let e = EventId::new(raw_id).unwrap();
            assert!(!e.is_internal());
            assert_eq!(e.get_raw(), raw_id);
        }

        #[test]
        fn user_event_ids_are_not_allowed_via_internal_constructor(raw_id in gen_raw_user_event_id()) {
            assert!(EventId::new_internal(raw_id).is_none());
        }

        #[test]
        fn internal_event_ids_are_allowed_via_internal_constructor(raw_id in gen_raw_internal_event_id()) {
            let e = EventId::new_internal(raw_id).unwrap();
            assert!(e.is_internal());
            assert_eq!(e.get_raw(), raw_id);
        }

        #[test]
        fn internal_event_ids_are_not_allowed_via_regular_new_constructor(raw_id in gen_raw_internal_event_id()) {
            assert!(EventId::new(raw_id).is_none());
        }

        #[test]
        fn invalid_event_ids_are_rejected(raw_id in gen_raw_invalid_event_id()) {
            assert_eq!(None, EventId::new(raw_id));
            assert_eq!(None, EventId::new_internal(raw_id));
        }
    }
}
