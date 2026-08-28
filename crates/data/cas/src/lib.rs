//! Userspace content-addressed storage.

mod r#async;
mod index;
mod service;

pub use bytes::Bytes;

pub use r#async::{AsyncCas, AsyncCasError, CasFuture, get_exact_fact};
pub use index::{AdmissionError, CasStats, IndexCas, InvalidRange, ResidentObject, SharedIndexCas};
pub use service::{
    ByteRange, CasService, CasServiceError, CasServiceFuture, CasUpload, ObjectRanges, PrefixHints,
    PrefixResolution, RangePart, StoredObject,
};

pub use covalence_logic_cas::{Cas, CasMut, CasShared};

use std::ops::Range;

use covalence_lib_hash::O256;

/// A CAS which can pin an object independently of subsequent store changes.
///
/// This userspace extension is useful for consumers such as virtual file
/// systems. The foundational [`Cas`] trait returns [`Bytes`] directly and does
/// not require an object type.
pub trait ObjectCas: Cas {
    /// An immutable object pinned independently of the CAS.
    type Object: CasObject<Error = Self::Error>;

    /// Opens and pins `address`, or returns `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup or I/O failure.
    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error>;
}

/// An immutable object pinned by [`ObjectCas::open`].
pub trait CasObject {
    /// Implementation-specific read failure.
    type Error: std::error::Error + 'static;

    /// Returns the object's length.
    fn len(&self) -> u64;

    /// Returns whether the object is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Reads exactly `range`.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific I/O or range failure.
    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error>;
}

/// Optional statistics for a concrete CAS view.
pub trait CasStatistics {
    /// Returns statistics for this view of the CAS.
    fn stats(&self) -> CasStats;
}
