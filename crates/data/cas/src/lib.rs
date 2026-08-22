//! Untrusted userspace content-addressed storage.
//!
//! [`MemoryCas`] stores opaque checked facts and implements
//! [`covalence_logic_cas::TrustedCas`]. The word "trusted" in that trait names
//! its checked result, not this store or its indexing policy.
//!
//! [`Cas`] and [`CasObject`] are the pre-fact range-reading API, retained while
//! existing consumers are restacked. Opening through that compatibility API
//! pins immutable bytes, so later removal affects only new opens. It introduces
//! no range or length LCF facts.

mod memory;

/// Bytes returned by [`CasObject::read`].
pub use bytes::Bytes;

pub use memory::{
    AdmissionError, CasStats, InvalidRange, MAX_OBJECT_BYTES, MemoryCas, MemoryCasError,
    ResidentObject,
};

use std::ops::Range;

use covalence_lib_hash::O256;

/// Legacy immutable byte-source interface retained during the fact restack.
///
/// This interface does not introduce checked LCF facts. New whole-object
/// consumers should use [`covalence_logic_cas::TrustedCas`] and
/// [`covalence_logic_cas::get_exact`].
pub trait Cas {
    /// Implementation-specific failure.
    type Error;

    /// An object opened from this source.
    type Object: CasObject<Error = Self::Error>;

    /// Opens and pins `address`, or returns `None` when absent.
    ///
    /// # Errors
    ///
    /// Returns an error when the source fails to answer at all, as distinct
    /// from answering that the address does not resolve.
    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error>;

    /// Returns the length of `address`, or `None` when it does not resolve.
    ///
    /// # Errors
    ///
    /// Returns an error when the source cannot determine the length.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
        Ok(self.open(address)?.map(|object| object.len()))
    }

    /// Reads exactly `range`, or returns `None` when absent.
    ///
    /// # Errors
    ///
    /// Returns an error when the range cannot be served or authenticated.
    fn read(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        self.open(address)?
            .map(|object| object.read(range))
            .transpose()
    }
}

/// An immutable object pinned by [`Cas::open`].
pub trait CasObject {
    /// Implementation-specific failure.
    type Error;

    /// Returns the object's length.
    fn len(&self) -> u64;

    /// Returns whether the object is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns exactly `range`; invalid or short reads fail.
    ///
    /// # Errors
    ///
    /// Returns an error when the range is invalid, cannot be served, or cannot
    /// be authenticated.
    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error>;
}
