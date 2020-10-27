//! Errors exposed in the ModalityProbe API.
//!
//! In order to be appropriate for embedded
//! use, these errors should be as tiny
//! and precise as possible.

use core::fmt;

/// Error that indicates an invalid event id was detected.
///
///
/// event ids must be greater than 0 and less than EventId::MAX_USER_ID
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct InvalidEventId;

#[cfg(feature = "std")]
impl std::error::Error for InvalidEventId {}

impl fmt::Display for InvalidEventId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Invalid Event Id")
    }
}

/// Error that indicates an invalid probe id was detected.
///
///
/// probe ids must be greater than 0 and less than ProbeId::MAX_ID
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct InvalidProbeId;

#[cfg(feature = "std")]
impl std::error::Error for InvalidProbeId {}

impl fmt::Display for InvalidProbeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Invalid Probe Id")
    }
}

/// Error that indicates an invalid wall clock time was detected.
///
/// Wall clock time must not be greater than Nanoseconds::MAX
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct InvalidWallClockTime;

#[cfg(feature = "std")]
impl std::error::Error for InvalidWallClockTime {}

impl fmt::Display for InvalidWallClockTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Invalid Nanoseconds wall clock time")
    }
}

/// An error relating to the '_with_time' APIs
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum WithTimeError {
    /// A provided primitive, unvalidated wall clock time
    /// turned out to be invalid.
    InvalidWallClockTime,
    /// A provided primitive, unvalidated event id
    /// turned out to be invalid.
    InvalidEventId,
}

#[cfg(feature = "std")]
impl std::error::Error for WithTimeError {}

impl fmt::Display for WithTimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WithTimeError::InvalidWallClockTime => InvalidWallClockTime.fmt(f),
            WithTimeError::InvalidEventId => InvalidWallClockTime.fmt(f),
        }
    }
}

impl From<InvalidWallClockTime> for WithTimeError {
    fn from(_e: InvalidWallClockTime) -> Self {
        WithTimeError::InvalidWallClockTime
    }
}

impl From<InvalidEventId> for WithTimeError {
    fn from(_e: InvalidEventId) -> Self {
        WithTimeError::InvalidEventId
    }
}

/// An error relating to the initialization
/// of an ModalityProbe instance from parts.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InitializationError {
    /// A provided primitive, unvalidated probe id
    /// turned out to be invalid.
    InvalidProbeId,
    /// A problem with the backing memory setup.
    StorageSetupError(StorageSetupError),
}

#[cfg(feature = "std")]
impl std::error::Error for InitializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            InitializationError::InvalidProbeId => None,
            InitializationError::StorageSetupError(e) => Some(e),
        }
    }
}

impl fmt::Display for InitializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InitializationError::InvalidProbeId => f.write_str("Invalid Probe Id"),
            InitializationError::StorageSetupError(_) => f.write_str("Storage Setup Error"),
        }
    }
}

impl From<StorageSetupError> for InitializationError {
    fn from(e: StorageSetupError) -> Self {
        InitializationError::StorageSetupError(e)
    }
}

/// An error relating to the initialization
/// of in-memory probe storage.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StorageSetupError {
    /// The provided storage space was insufficient
    /// to support a minimally useful probe
    /// implementation.
    UnderMinimumAllowedSize,
    /// The provided space for clock-buckets and logging
    /// exceeded the number of units the probe implementation
    /// can track.
    ExceededMaximumAddressableSize,
    /// The provided or computed output pointer for
    /// probe data storage turned out to be null.
    NullDestination,
}

#[cfg(feature = "std")]
impl std::error::Error for StorageSetupError {}

impl fmt::Display for StorageSetupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StorageSetupError::UnderMinimumAllowedSize => {
                f.write_str("Storage under minimum allowed size")
            }
            StorageSetupError::ExceededMaximumAddressableSize => {
                f.write_str("Storage exceeds maximum addressable size")
            }
            StorageSetupError::NullDestination => f.write_str("Null destination pointer"),
        }
    }
}

/// The errors than can occur when producing a probe's
/// causal history for use by some other probe instance.
///
/// Returned in the error cases for the `produce_snapshot` and
/// `produce_snapshot_bytes` functions.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ProduceError {
    /// The destination that is receiving the history is not big enough.
    ///
    /// Indicates that the end user should provide a larger destination buffer.
    InsufficientDestinationSize,
}

#[cfg(feature = "std")]
impl std::error::Error for ProduceError {}

impl fmt::Display for ProduceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Insufficient destination size")
    }
}

/// The errors than can occur when merging in the causal history from some
/// other probe instance.
///
/// Returned in the error cases for the `merge_snapshot` and
/// `merge_fixed_size_snapshot` functions.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MergeError {
    /// The local probe does not have enough space to track all
    /// of direct neighbors attempting to communicate with it.
    ExceededAvailableClocks,
    /// The the external history source buffer we attempted to merge
    /// was insufficiently sized for a valid causal snapshot.
    InsufficientSourceSize,
    /// The external history violated a semantic rule of the protocol,
    /// such as by having a probe_id out of the allowed value range.
    ExternalHistorySemantics,
}

#[cfg(feature = "std")]
impl std::error::Error for MergeError {}

impl fmt::Display for MergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MergeError::ExceededAvailableClocks => f.write_str("Exceeded available clocks"),
            MergeError::InsufficientSourceSize => f.write_str("Insufficient source size"),
            MergeError::ExternalHistorySemantics => {
                f.write_str("External history semantic violation")
            }
        }
    }
}

/// The error relating to using the `report` method to
/// produce a full causal history log report.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReportError {
    /// The destination that is receiving the report is not big enough.
    ///
    /// Indicates that the end user should provide a larger destination buffer.
    InsufficientDestinationSize,
}

#[cfg(feature = "std")]
impl std::error::Error for ReportError {}

impl fmt::Display for ReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReportError::InsufficientDestinationSize => {
                f.write_str("Insufficient destination size")
            }
        }
    }
}

/// General purpose error that captures all errors that arise
/// from using the ModalityProbe APIs.
///
/// Not directly returned by any of the public APIs, but provided
/// as a convenience for catch-all error piping.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ModalityProbeError {
    /// Error that indicates an invalid event id was detected.
    ///
    /// Event ids must be greater than 0 and less than EventId::MAX_USER_ID
    InvalidEventId,
    /// Error that indicates an invalid probe id was detected.
    ///
    /// Probe ids must be greater than 0 and less than ProbeId::MAX_ID
    InvalidProbeId,
    /// An error relating to the initialization of an ModalityProbe instance.
    InitializationError(InitializationError),
    /// The errors than can occur when using the `produce_snapshot`
    /// and `produce_snapshot_bytes` functions.
    ProduceError(ProduceError),
    /// The errors than can occur when using the `merge_snapshot`
    /// and `merge_fixed_size_snapshot` functions.
    MergeError(MergeError),
    /// The error relating to using the `report` method to
    /// produce a full causal history log report.
    ReportError(ReportError),
}

#[cfg(feature = "std")]
impl std::error::Error for ModalityProbeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ModalityProbeError::InvalidEventId => None,
            ModalityProbeError::InvalidProbeId => None,
            ModalityProbeError::InitializationError(e) => Some(e),
            ModalityProbeError::ProduceError(e) => Some(e),
            ModalityProbeError::MergeError(e) => Some(e),
            ModalityProbeError::ReportError(e) => Some(e),
        }
    }
}

impl fmt::Display for ModalityProbeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModalityProbeError::InvalidEventId => f.write_str("Invalid Event Id"),
            ModalityProbeError::InvalidProbeId => f.write_str("Invalid Probe Id"),
            ModalityProbeError::InitializationError(_) => f.write_str("Initialization Error"),
            ModalityProbeError::ProduceError(_) => f.write_str("Produce Snapshot Error"),
            ModalityProbeError::MergeError(_) => f.write_str("Merge Snapshot Error"),
            ModalityProbeError::ReportError(_) => f.write_str("Report Error"),
        }
    }
}

impl From<InvalidEventId> for ModalityProbeError {
    #[inline]
    fn from(_: InvalidEventId) -> Self {
        ModalityProbeError::InvalidEventId
    }
}

impl From<InvalidProbeId> for ModalityProbeError {
    #[inline]
    fn from(_: InvalidProbeId) -> Self {
        ModalityProbeError::InvalidProbeId
    }
}

impl From<InitializationError> for ModalityProbeError {
    #[inline]
    fn from(e: InitializationError) -> Self {
        ModalityProbeError::InitializationError(e)
    }
}

impl From<ProduceError> for ModalityProbeError {
    #[inline]
    fn from(e: ProduceError) -> Self {
        ModalityProbeError::ProduceError(e)
    }
}

impl From<MergeError> for ModalityProbeError {
    #[inline]
    fn from(e: MergeError) -> Self {
        ModalityProbeError::MergeError(e)
    }
}

impl From<ReportError> for ModalityProbeError {
    #[inline]
    fn from(e: ReportError) -> Self {
        ModalityProbeError::ReportError(e)
    }
}

impl From<StorageSetupError> for ModalityProbeError {
    #[inline]
    fn from(e: StorageSetupError) -> Self {
        ModalityProbeError::InitializationError(InitializationError::StorageSetupError(e))
    }
}
