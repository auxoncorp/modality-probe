//! Identifiers critical to the Modality probe system

use crate::{InvalidEventId, InvalidGeneratedId, InvalidInstanceId, InvalidProbeId};
use core::convert::{TryFrom, TryInto};
use core::num::NonZeroU32;
use static_assertions::{assert_eq_align, assert_eq_size};

assert_eq_size!(u32, ProbeId);
assert_eq_align!(u32, ProbeId);

/// Ought to uniquely identify a probe for where events occur within a system under test.
///
/// Typically represents a single thread.
///
/// Must be backed by a value greater than 0 and less than or equal to
/// ProbeId::MAX_ID.
///
/// A ProbeId is composed of a runtime InstanceId and a build-time GeneratedId.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
pub struct ProbeId(
    /* Never make this inner field truly public */ pub(crate) NonZeroU32,
);

impl ProbeId {
    /// The largest permissible backing id value
    pub const MAX_ID: u32 = 0b0011_1111_1111_1111_1111_1111_1111_1111;

    /// Createa ProbeId from a raw primitive
    ///
    /// raw_id is composed of a GeneratedId and an InstanceId.
    /// It must be greater than 0 and less than 0b0100_0000_0000_0000_0000_0000_0000_0000
    #[inline]
    pub const fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_ID || (raw_id & GeneratedId::MAX_ID) == 0 {
            return None;
        }
        match NonZeroU32::new(raw_id) {
            Some(id) => Some(Self(id)),
            None => None,
        }
    }

    /// Createa ProbeId from a raw primitive
    ///
    /// raw_id is composed of a GeneratedId and an InstanceId
    ///
    /// # Safety
    ///
    /// raw_id must be greater than 0 and less than 0b0100_0000_0000_0000_0000_0000_0000_0000
    pub const unsafe fn new_unchecked(raw_id: u32) -> Self {
        Self(NonZeroU32::new_unchecked(raw_id))
    }

    /// Create a ProbeId from GeneratedId and InstanceId parts
    #[inline]
    pub fn from_parts(generated_id: GeneratedId, instance_id: InstanceId) -> Self {
        let raw = generated_id.get_raw() | (instance_id.get() as u32) << InstanceId::FIELD_OFFSET;
        Self::new(raw).expect("Can't create a ProbeId using an invalid GeneratedId")
    }

    /// Get the underlying value with Rust's assurances
    /// of non-zero-ness.
    #[inline]
    pub const fn get(self) -> NonZeroU32 {
        self.0
    }

    /// Get the underlying value as a convenient primitive
    #[inline]
    pub const fn get_raw(self) -> u32 {
        self.0.get()
    }

    /// Get the InstanceId portion of the ProbeID
    #[inline]
    pub const fn instance_id(self) -> InstanceId {
        let raw = (self.get_raw() >> InstanceId::FIELD_OFFSET) & InstanceId::MAX_ID as u32;
        InstanceId(raw as u8)
    }

    /// Get the GeneratedId portion of the ProbeID
    #[inline]
    pub const fn generated_id(self) -> Option<GeneratedId> {
        GeneratedId::new(self.get_raw() & GeneratedId::MAX_ID)
    }

    /// Get the GeneratedId portion of the ProbeID without checks
    ///
    /// # Safety
    ///
    /// The GeneratedId portion of the ProbeId must be greater than zero
    #[inline]
    pub const unsafe fn generated_id_unchecked(self) -> GeneratedId {
        GeneratedId(NonZeroU32::new_unchecked(
            self.get_raw() & GeneratedId::MAX_ID,
        ))
    }
}

impl From<ProbeId> for NonZeroU32 {
    #[inline]
    fn from(t: ProbeId) -> Self {
        t.0
    }
}

impl From<ProbeId> for u32 {
    #[inline]
    fn from(t: ProbeId) -> Self {
        t.0.get()
    }
}

/// Part of the ProbeId, a generated non-zero 24-bit identifier.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
pub struct GeneratedId(NonZeroU32);

impl GeneratedId {
    /// The largest permissible backing id value
    pub const MAX_ID: u32 = 0b0000_0000_1111_1111_1111_1111_1111_1111;
    /// The bit width of a GeneratedId
    pub const FIELD_WIDTH: usize = 24;
    /// The bit offset of a GeneratedId within a ProbeId
    pub const FIELD_OFFSET: usize = 0;

    /// Create a new GeneratedId, raw_id must be less than Self::MAX_ID
    #[inline]
    pub const fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_ID {
            return None;
        }
        match NonZeroU32::new(raw_id) {
            Some(id) => Some(Self(id)),
            None => None,
        }
    }

    /// Get the underlying value with Rust's assurances
    /// of non-zero-ness.
    #[inline]
    pub const fn get(self) -> NonZeroU32 {
        self.0
    }

    /// Get the underlying value as a convenient primitive
    #[inline]
    pub const fn get_raw(self) -> u32 {
        self.0.get()
    }
}

impl From<GeneratedId> for NonZeroU32 {
    #[inline]
    fn from(id: GeneratedId) -> Self {
        id.0
    }
}

impl From<GeneratedId> for u32 {
    #[inline]
    fn from(id: GeneratedId) -> Self {
        id.0.get()
    }
}

/// Part of the ProbeId, a 6-bit runtime identifier user-supplied at probe initialization
/// used to indicate a particular instance of a probe.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(
    feature = "std",
    derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)
)]
pub struct InstanceId(u8);

impl InstanceId {
    /// The largest permissible backing id value
    pub const MAX_ID: u8 = 0b0011_1111;
    /// The bit width of an InstanceId
    pub const FIELD_WIDTH: usize = 6;
    /// The bit offset of an InstanceId within a ProbeId
    pub const FIELD_OFFSET: usize = 24;

    /// Create a new InstanceId, raw_id must be less than Self::MAX_ID
    pub const fn new(raw_id: u8) -> Option<Self> {
        if raw_id > Self::MAX_ID {
            None
        } else {
            Some(Self(raw_id))
        }
    }

    /// Get the underlying value
    #[inline]
    pub const fn get(self) -> u8 {
        self.0
    }
}

impl From<InstanceId> for u8 {
    #[inline]
    fn from(id: InstanceId) -> Self {
        id.get()
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

infallible_sizing_try_from_impl!(u8, ProbeId, InvalidProbeId, InvalidProbeId);
infallible_sizing_try_from_impl!(u16, ProbeId, InvalidProbeId, InvalidProbeId);
infallible_sizing_try_from_impl!(u32, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(u64, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(u128, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(usize, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(i8, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(i16, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(i32, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(i64, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(i128, ProbeId, InvalidProbeId, InvalidProbeId);
fallible_sizing_try_from_impl!(isize, ProbeId, InvalidProbeId, InvalidProbeId);

infallible_sizing_try_from_impl!(u8, InstanceId, InvalidInstanceId, InvalidInstanceId);

infallible_sizing_try_from_impl!(u8, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
infallible_sizing_try_from_impl!(u16, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
infallible_sizing_try_from_impl!(u32, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(u64, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(u128, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(usize, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(i8, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(i16, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(i32, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(i64, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(i128, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);
fallible_sizing_try_from_impl!(isize, GeneratedId, InvalidGeneratedId, InvalidGeneratedId);

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

assert_eq_size!(u32, EventId);
assert_eq_align!(u32, EventId);

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
    /// probe implementation.
    pub const NUM_RESERVED_IDS: u32 = 256;
    /// The maximum-permissible id value for for an Event
    /// defined by end users.
    pub const MAX_USER_ID: u32 = EventId::MAX_INTERNAL_ID - EventId::NUM_RESERVED_IDS;

    /// The probe produced a log report for transmission to the backend
    /// for external analysis.
    pub const EVENT_PRODUCED_EXTERNAL_REPORT: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 1) });
    /// Some log entries were overwritten before getting reported, the number of missed
    /// entries is stored in the payload.
    pub const EVENT_LOG_ITEMS_MISSED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 2) });
    /// A logical clock's count reached the maximum trackable value.
    /// The next sequence id / epoch is stored in the payload.
    /// If this probe is tracking restarts, then the next sequence id is provided
    /// by the user's backing implementation.
    pub const EVENT_LOGICAL_CLOCK_OVERFLOWED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 3) });
    /// The local instance (e.g. Modality probe) did not have enough memory
    /// reserved to store enough logical clocks to track all of the unique
    /// neighbors that attempt to communicate with it.
    pub const EVENT_NUM_CLOCKS_OVERFLOWED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 4) });
    /// The report destination buffer is too small to fit a header and/or the frontier clocks
    pub const EVENT_INSUFFICIENT_REPORT_BUFFER_SIZE: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 5) });
    /// The probe successfully initialized itself.
    pub const EVENT_PROBE_INITIALIZED: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 6) });
    /// The probe is configured to track restarts, but the user's implementation
    /// returned an invalid zero value or a None option variant.
    pub const EVENT_INVALID_NEXT_EPOCH_SEQ_ID: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 7) });
    /// Reserved for indicating wall clock time
    pub const EVENT_WALL_CLOCK_TIME_ONLY: EventId =
        EventId(unsafe { NonZeroU32::new_unchecked(EventId::MAX_INTERNAL_ID - 8) });

    /// The events reserved for internal use
    pub const INTERNAL_EVENTS: &'static [EventId] = &[
        EventId::EVENT_PRODUCED_EXTERNAL_REPORT,
        EventId::EVENT_LOG_ITEMS_MISSED,
        EventId::EVENT_LOGICAL_CLOCK_OVERFLOWED,
        EventId::EVENT_NUM_CLOCKS_OVERFLOWED,
        EventId::EVENT_INSUFFICIENT_REPORT_BUFFER_SIZE,
        EventId::EVENT_PROBE_INITIALIZED,
        EventId::EVENT_INVALID_NEXT_EPOCH_SEQ_ID,
        EventId::EVENT_WALL_CLOCK_TIME_ONLY,
    ];

    /// raw_id must be greater than 0 and less than EventId::MAX_USER_ID
    #[inline]
    pub const fn new(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_USER_ID {
            return None;
        }
        match NonZeroU32::new(raw_id) {
            Some(id) => Some(Self(id)),
            None => None,
        }
    }

    /// # Safety
    ///
    /// raw_id must be greater than 0 and less than EventId::MAX_USER_ID
    pub const unsafe fn new_unchecked(raw_id: u32) -> Self {
        Self(NonZeroU32::new_unchecked(raw_id))
    }

    /// A means of generating ids for internal protocol use.
    /// raw_id must be greater than EventId::MAX_USER_ID and
    /// less than or equal to EventId::MAX_INTERNAL_ID
    #[inline]
    pub const fn new_internal(raw_id: u32) -> Option<Self> {
        if raw_id > Self::MAX_USER_ID && raw_id <= Self::MAX_INTERNAL_ID {
            match NonZeroU32::new(raw_id) {
                Some(id) => Some(Self(id)),
                None => None,
            }
        } else {
            None
        }
    }

    /// Get the underlying value with Rust's assurances
    /// of non-zero-ness.
    #[inline]
    pub const fn get(self) -> NonZeroU32 {
        self.0
    }

    /// Get the underlying value as a convenient primitive
    #[inline]
    pub const fn get_raw(self) -> u32 {
        self.0.get()
    }

    /// Is this id part of the set of IDs reserved for internal
    /// protocol use?
    #[inline]
    pub const fn is_internal(self) -> bool {
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

    impl ValueTree for EventIdBinarySearch {
        type Value = EventId;

        fn current(&self) -> EventId {
            let x = self.0.current();
            let x1 = core::cmp::max(1, core::cmp::min(x, EventId::MAX_USER_ID));
            EventId(unsafe { NonZeroU32::new_unchecked(x1) })
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

    /// A proptest value tree for probe ids. It builds off of u32's
    /// binary search.
    pub struct ProbeIdBinarySearch(BinarySearch);

    impl ValueTree for ProbeIdBinarySearch {
        type Value = ProbeId;

        fn current(&self) -> ProbeId {
            let x = self.0.current();
            let x1 = core::cmp::max(1, core::cmp::min(x, ProbeId::MAX_ID));
            ProbeId(unsafe { NonZeroU32::new_unchecked(x1) })
        }

        fn simplify(&mut self) -> bool {
            self.0.simplify()
        }

        fn complicate(&mut self) -> bool {
            self.0.complicate()
        }
    }

    #[derive(Debug)]
    /// A proptest strategy to be used for any valid probe id.
    pub struct AnyProbeId;

    impl Strategy for AnyProbeId {
        type Tree = ProbeIdBinarySearch;
        type Value = ProbeId;

        fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
            Ok(ProbeIdBinarySearch(BinarySearch::new(
                runner.rng().next_u32().saturating_add(1),
            )))
        }
    }

    impl Arbitrary for ProbeId {
        type Parameters = ();
        type Strategy = AnyProbeId;

        fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
            AnyProbeId
        }
    }
}

#[cfg(feature = "std")]
pub use prop::*;

#[cfg(test)]
pub(crate) mod id_tests {
    use super::*;
    use crate::{ProbeEpoch, ProbeTicks};
    use proptest::prelude::*;

    #[test]
    fn new_ids_cannot_have_zero_values() {
        assert!(ProbeId::new(0).is_none());
        assert!(GeneratedId::new(0).is_none());
        assert!(EventId::new(0).is_none());
        assert!(EventId::new_internal(0).is_none());
    }

    #[test]
    fn boundary_values() {
        assert!(ProbeId::new(ProbeId::MAX_ID).is_some());
        assert!(GeneratedId::new(GeneratedId::MAX_ID).is_some());
        assert!(InstanceId::new(InstanceId::MAX_ID).is_some());

        assert!(EventId::new(EventId::MAX_USER_ID).is_some());
        assert!(EventId::new_internal(EventId::MAX_INTERNAL_ID).is_some());

        assert!(EventId::new_internal(EventId::MAX_USER_ID).is_none());
        assert!(EventId::new(EventId::MAX_INTERNAL_ID).is_none());
    }

    prop_compose! {
        pub(crate) fn gen_raw_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> u32 {
            raw_id
        }
    }

    prop_compose! {
        pub(crate) fn gen_probe_id()(raw_id in 1..=ProbeId::MAX_ID) -> ProbeId {
            raw_id.try_into().unwrap()
        }
    }

    prop_compose! {
        pub(crate) fn gen_generated_id()(raw_id in 1..=GeneratedId::MAX_ID) -> GeneratedId {
            raw_id.try_into().unwrap()
        }
    }

    prop_compose! {
        pub(crate) fn gen_instance_id()(raw_id in 0..=InstanceId::MAX_ID) -> InstanceId {
            raw_id.try_into().unwrap()
        }
    }

    pub(crate) fn gen_probe_epoch() -> impl Strategy<Value = ProbeEpoch> {
        any::<ProbeEpoch>()
    }

    pub(crate) fn gen_probe_ticks() -> impl Strategy<Value = ProbeTicks> {
        any::<ProbeTicks>()
    }

    prop_compose! {
        fn gen_raw_invalid_probe_id()(raw_id in (ProbeId::MAX_ID+1)..core::u32::MAX) -> u32 {
            raw_id
        }
    }

    proptest! {
        #[test]
        fn valid_probe_ids_are_accepted(raw_id in gen_raw_probe_id()) {
            let t = ProbeId::new(raw_id).unwrap();
            assert_eq!(t.get_raw(), raw_id);
        }

        #[test]
        fn invalid_probe_ids_are_rejected(raw_id in gen_raw_invalid_probe_id()) {
            assert_eq!(None, ProbeId::new(raw_id));
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

        #[test]
        fn round_trip_composite_probe_id(gend_id in gen_generated_id(), inst_id in gen_instance_id()) {
            prop_assert_eq!(Some(gend_id), GeneratedId::new(gend_id.get_raw()));
            prop_assert_eq!(Some(inst_id), InstanceId::new(inst_id.get()));
            let probe_id = ProbeId::from_parts(gend_id, inst_id);
            prop_assert_eq!(probe_id.generated_id(), Some(gend_id));
            prop_assert_eq!(unsafe { probe_id.generated_id_unchecked() }, gend_id);
            prop_assert_eq!(probe_id.instance_id(), inst_id);
            prop_assert_eq!(probe_id.get_raw() & GeneratedId::MAX_ID, gend_id.get_raw());
            prop_assert_eq!((probe_id.get_raw() >> GeneratedId::FIELD_WIDTH) as u8 & InstanceId::MAX_ID, inst_id.get());
            prop_assert_eq!((probe_id.get_raw() >> InstanceId::FIELD_OFFSET) as u8 & InstanceId::MAX_ID, inst_id.get());
            prop_assert_eq!(probe_id.get_raw(), gend_id.get_raw() | ((inst_id.get() as u32) << GeneratedId::FIELD_WIDTH));
            prop_assert_eq!(probe_id.get_raw(), gend_id.get_raw() | ((inst_id.get() as u32) << InstanceId::FIELD_OFFSET));
        }
    }
}
