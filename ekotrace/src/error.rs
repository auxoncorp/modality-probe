//! Errors exposed in the Ekotrace API.
//!
//! In order to be appropriate for embedded
//! use, these errors should be as tiny
//! and precise as possible.

/// Error that indicates an invalid event id was detected.
///
///
/// event ids must be greater than 0 and less than EventId::MAX_USER_ID
#[derive(Debug, Clone, Copy)]
pub struct InvalidEventId;

/// Error that indicates an invalid tracer id was detected.
///
///
/// tracer ids must be greater than 0 and less than TracerId::MAX_ID
#[derive(Debug, Clone, Copy)]
pub struct InvalidTracerId;

/// An error relating to the initialization
/// of an Ekotrace instance from parts.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum InitializationError {
    /// A provided primitive, unvalidated tracer id
    /// turned out to be invalid.
    InvalidTracerId,
    /// A problem with the backing memory setup.
    StorageSetupError(StorageSetupError),
}

/// An error relating to the initialization
/// of in-memory tracing storage.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StorageSetupError {
    /// The provided storage space was insufficient
    /// to support a minimally useful tracing
    /// implementation.
    UnderMinimumAllowedSize,
    /// The provided space for clock-buckets and logging
    /// exceeded the number of units the tracing implementation
    /// can track.
    ExceededMaximumAddressableSize,
    /// The provided or computed output pointer for
    /// tracing data storage turned out to be null.
    NullDestination,
}

/// The errors than can occur when distributing (exporting a serialized
/// version of) a tracer's causal history for use by some other tracer instance.
///
/// Returned in the error cases for the `distribute_snapshot` and
/// `distribute_fixed_size_snapshot` functions
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DistributeError {
    /// The destination that is receiving the history is not big enough.
    ///
    /// Indicates that the end user should provide a larger destination buffer.
    InsufficientDestinationSize,
    /// An unexpected error occurred while writing out causal history.
    ///
    /// Indicates a logical error in the implementation of this library
    /// (or its dependencies).
    Encoding,
}

/// The errors than can occur when merging in the causal history from some
/// other tracer instance.
///
/// Returned in the error cases for the `merge_snapshot` and
/// `merge_fixed_size_snapshot` functions.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MergeError {
    /// The local tracer does not have enough space to track all
    /// of direct neighbors attempting to communicate with it.
    ExceededAvailableClocks,
    /// The the external history we attempted to merge was encoded
    /// in an invalid fashion.
    ExternalHistoryEncoding,
    /// The external history violated a semantic rule of the protocol,
    /// such as by having a tracer_id out of the allowed value range.
    ExternalHistorySemantics,
}
/// The error relating to using the `report` method to
/// produce a full causal history log report.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReportError {
    /// The destination that is receiving the report is not big enough.
    ///
    /// Indicates that the end user should provide a larger destination buffer.
    InsufficientDestinationSize,
    /// An unexpected error occurred while writing out the report.
    ///
    /// Indicates a logical error in the implementation of this library
    /// (or its dependencies).
    Encoding,
}

/// General purpose error that captures all errors that arise
/// from using the Ekotrace APIs.
///
/// Not directly returned by any of the public APIs, but provided
/// as a convenience for catch-all error piping.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EkotraceError {
    /// Error that indicates an invalid event id was detected.
    ///
    /// Event ids must be greater than 0 and less than EventId::MAX_USER_ID
    InvalidEventId,
    /// Error that indicates an invalid tracer id was detected.
    ///
    /// Tracer ids must be greater than 0 and less than TracerId::MAX_ID
    InvalidTracerId,
    /// An error relating to the initialization of an Ekotrace instance.
    InitializationError(InitializationError),
    /// The errors than can occur when using the `distribute_snapshot`
    /// and `distribute_fixed_size_snapshot` functions.
    DistributeError(DistributeError),
    /// The errors than can occur when using the `merge_snapshot`
    /// and `merge_fixed_size_snapshot` functions.
    MergeError(MergeError),
    /// The error relating to using the `report` method to
    /// produce a full causal history log report.
    ReportError(ReportError),
}

impl From<InvalidEventId> for EkotraceError {
    #[inline]
    fn from(_: InvalidEventId) -> Self {
        EkotraceError::InvalidEventId
    }
}

impl From<InvalidTracerId> for EkotraceError {
    #[inline]
    fn from(_: InvalidTracerId) -> Self {
        EkotraceError::InvalidTracerId
    }
}

impl From<InitializationError> for EkotraceError {
    #[inline]
    fn from(e: InitializationError) -> Self {
        EkotraceError::InitializationError(e)
    }
}

impl From<DistributeError> for EkotraceError {
    #[inline]
    fn from(e: DistributeError) -> Self {
        EkotraceError::DistributeError(e)
    }
}

impl From<MergeError> for EkotraceError {
    #[inline]
    fn from(e: MergeError) -> Self {
        EkotraceError::MergeError(e)
    }
}

impl From<ReportError> for EkotraceError {
    #[inline]
    fn from(e: ReportError) -> Self {
        EkotraceError::ReportError(e)
    }
}

impl From<StorageSetupError> for EkotraceError {
    #[inline]
    fn from(e: StorageSetupError) -> Self {
        EkotraceError::InitializationError(InitializationError::StorageSetupError(e))
    }
}