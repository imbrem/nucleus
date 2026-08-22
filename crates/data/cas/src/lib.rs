//! Userspace content-addressed storage.

mod index;

/// Bytes returned by [`CasObject::read`].
pub use bytes::Bytes;

pub use index::{AdmissionError, CasStats, IndexCas, InvalidRange, ResidentObject, SharedIndexCas};

pub use covalence_logic_cas::{Cas, CasMut, CasObject, CasShared};

/// Optional statistics for a concrete CAS view.
pub trait CasStatistics {
    /// Returns statistics for this view of the CAS.
    fn stats(&self) -> CasStats;
}
