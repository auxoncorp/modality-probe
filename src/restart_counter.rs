use crate::ProbeId;
use core::fmt;

/// A persistent restart sequence counter
pub trait RestartCounter {
    /// Get the next persistent sequence number.
    ///
    /// This method is called when a probe initializes to get the initial
    /// epoch portion of the clock, and each time the ticks portion of the
    /// clock overflows during the probe's lifetime.
    ///
    /// The sequence number should start at zero, and be monotonically increased by a step size of
    /// one after each retrieval.
    ///
    /// When the sequence number reaches its maximum value (0xFFFF), it
    /// should wrap around to the value 0.
    fn next_sequence_id(&mut self, probe_id: ProbeId) -> Result<u16, RestartSequenceIdUnavailable>;
}

/// Either:
/// * The user-supplied restart persistence counter failed
/// to produce the next sequence id.
/// * No restart persistence strategy was provided by the user
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RestartSequenceIdUnavailable;

impl fmt::Debug for RestartSequenceIdUnavailable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("No restart sequence id could be produced")
    }
}

/// C function type for retrieving the next persistent sequence number.
/// Populates the next sequence number in `out_sequence_id`
///
/// Returns `MODALITY_PROBE_ERROR_OK` (0) when things are ok,
/// and `MODALITY_PROBE_ERROR_RESTART_PERSISTENCE_SEQUENCE_ID_UNAVAILABLE` (9) when the
/// next sequence number could not be determined.
#[allow(non_camel_case_types)]
pub type next_sequence_id_fn =
    extern "C" fn(probe_id: u32, state: *mut core::ffi::c_void, out_sequence_id: *mut u16) -> usize;

/// A persistent restart sequence counter provider backed by a C implementation
pub struct CRestartCounterProvider {
    /// C interface for retrieving the next persistent sequence number
    pub iface: next_sequence_id_fn,
    /// User's state provided to the next_sequence_id_fn function call
    pub state: *mut core::ffi::c_void,
}

impl RestartCounter for CRestartCounterProvider {
    fn next_sequence_id(&mut self, probe_id: ProbeId) -> Result<u16, RestartSequenceIdUnavailable> {
        let mut out_sequence_number: u16 = 0;
        let res = (self.iface)(
            probe_id.get_raw(),
            self.state,
            &mut out_sequence_number as *mut u16,
        );
        // The "OK" case
        if res == 0 {
            Ok(out_sequence_number)
        } else {
            Err(RestartSequenceIdUnavailable)
        }
    }
}

/// A persistent restart sequence counter provider backed by a Rust implementation
pub struct RustRestartCounterProvider<'a> {
    /// Rust interface for retrieving the next persistent sequence number
    pub iface: &'a mut dyn RestartCounter,
}

/// A persistent restart sequence counter provider
pub enum RestartCounterProvider<'a> {
    /// Do no restart handling for this probe.
    /// Any events logged after a restart will be seen as duplicates.
    NoRestartTracking,
    /// A persistent restart sequence counter provider backed by a C implementation
    C(CRestartCounterProvider),
    /// A persistent restart sequence counter provider backed by a Rust implementation
    Rust(RustRestartCounterProvider<'a>),
}

impl<'a> RestartCounterProvider<'a> {
    /// Returns true if the user has provided some function at probe
    /// initialization time which will be responsible for providing
    /// a restart-persistence sequence number.
    pub fn is_tracking_restarts(&self) -> bool {
        !matches!(&self, RestartCounterProvider::NoRestartTracking)
    }
}

impl<'a> From<&'a mut dyn RestartCounter> for RestartCounterProvider<'a> {
    fn from(r: &'a mut dyn RestartCounter) -> Self {
        RestartCounterProvider::Rust(RustRestartCounterProvider { iface: r })
    }
}

impl<'a> RestartCounter for RestartCounterProvider<'a> {
    fn next_sequence_id(&mut self, probe_id: ProbeId) -> Result<u16, RestartSequenceIdUnavailable> {
        match self {
            RestartCounterProvider::NoRestartTracking => Err(RestartSequenceIdUnavailable),
            RestartCounterProvider::C(c) => c.next_sequence_id(probe_id),
            RestartCounterProvider::Rust(r) => r.iface.next_sequence_id(probe_id),
        }
    }
}

impl<'a> fmt::Debug for RestartCounterProvider<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RestartCounterProvider::NoRestartTracking => {
                write!(f, "RestartCounterProvider::NoRestartTracking")?
            }
            RestartCounterProvider::C(_) => write!(f, "RestartCounterProvider::C")?,
            RestartCounterProvider::Rust(_) => write!(f, "RestartCounterProvider::Rust")?,
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_restart_tracking() {
        let mut rsc = RestartCounterProvider::NoRestartTracking;
        assert_eq!(rsc.is_tracking_restarts(), false);
        assert_eq!(
            rsc.next_sequence_id(ProbeId::new(1).unwrap()),
            Err(RestartSequenceIdUnavailable)
        );
    }
}
