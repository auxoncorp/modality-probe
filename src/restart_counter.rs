use crate::ProbeId;
use core::fmt;

/// The persistent sequence number value returned when this
/// probe is not tracking restarts.
pub const NO_RESTART_TRACKING_SEQUENCE_NUMBER: u16 = 0;

/// A persistent restart sequence counter
pub trait RestartCounter {
    /// Get the next persistent sequence number
    fn next_sequence_id(&mut self, probe_id: ProbeId) -> u16;
}

/// C function type for retrieving the next persistent sequence number
#[allow(non_camel_case_types)]
pub type next_sequence_id_fn = extern "C" fn(u32, *mut core::ffi::c_void) -> u16;

/// A persistent restart sequence counter provider backed by a C implementation
pub struct CRestartCounterProvider {
    /// C interface for retrieving the next persistent sequence number
    pub iface: next_sequence_id_fn,
    /// User's state provided to the next_sequence_id_fn function call
    pub state: *mut core::ffi::c_void,
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

impl<'a> From<&'a mut dyn RestartCounter> for RestartCounterProvider<'a> {
    fn from(r: &'a mut dyn RestartCounter) -> Self {
        RestartCounterProvider::Rust(RustRestartCounterProvider { iface: r })
    }
}

impl<'a> RestartCounterProvider<'a> {
    fn next_sequence_id(&mut self, probe_id: ProbeId) -> u16 {
        match self {
            RestartCounterProvider::NoRestartTracking => NO_RESTART_TRACKING_SEQUENCE_NUMBER,
            RestartCounterProvider::C(c) => (c.iface)(probe_id.get_raw(), c.state),
            RestartCounterProvider::Rust(r) => r.iface.next_sequence_id(probe_id),
        }
    }
}

#[derive(Debug)]
pub(crate) struct RestartSequenceCounter<'a> {
    provider: RestartCounterProvider<'a>,
}

impl<'a> RestartSequenceCounter<'a> {
    pub fn new(provider: RestartCounterProvider<'a>) -> Self {
        RestartSequenceCounter { provider }
    }

    pub fn is_tracking_restarts(&self) -> bool {
        !matches!(&self.provider, RestartCounterProvider::NoRestartTracking)
    }

    pub fn next_sequence_id(&mut self, probe_id: ProbeId) -> u16 {
        self.provider.next_sequence_id(probe_id)
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
        let mut rsc = RestartSequenceCounter::new(RestartCounterProvider::NoRestartTracking);
        assert_eq!(rsc.is_tracking_restarts(), false);
        assert_eq!(
            rsc.next_sequence_id(ProbeId::new(1).unwrap()),
            NO_RESTART_TRACKING_SEQUENCE_NUMBER
        );
    }
}
