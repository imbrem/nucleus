use covalence_lib_error::snafu::Snafu;

use crate::{Bytes, O256};

/// An unchecked claim that `blob` has the given content hash.
///
/// Constructing an assertion establishes no invariant. Call [`Self::check`]
/// to hash the complete blob and introduce a [`CasFact`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasAssertion {
    /// Claimed `O256` hash of the complete blob.
    pub hash: O256,
    /// Complete claimed blob.
    pub blob: Bytes,
}

impl CasAssertion {
    /// Constructs an unchecked assertion without hashing `blob`.
    #[must_use]
    pub fn new(hash: O256, blob: impl Into<Bytes>) -> Self {
        Self {
            hash,
            blob: blob.into(),
        }
    }

    /// Checks the claimed address against every byte of the blob.
    ///
    /// # Errors
    ///
    /// Returns [`CasCheckError`] when the computed and claimed addresses
    /// differ.
    pub fn check(self) -> Result<CasFact, CasCheckError> {
        let computed = O256::from_bytes(&self.blob);
        if computed == self.hash {
            Ok(CasFact { assertion: self })
        } else {
            Err(CasCheckError {
                claimed: self.hash,
                computed,
            })
        }
    }
}

/// Failure to validate a whole-object CAS assertion.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("claimed hash {claimed} does not match computed hash {computed}"))]
pub struct CasCheckError {
    /// Hash claimed by the assertion.
    pub claimed: O256,
    /// Hash computed over all of the assertion's bytes.
    pub computed: O256,
}

/// A checked fact that a complete blob has an `O256` hash.
///
/// This is the erased runtime counterpart of Lean's `Nucleus.CasPair`. Its
/// private representation is the LCF boundary: safe code can inspect and clone
/// a fact, but only the checking rules in this module can construct one.
///
/// In Lean, [`Self::from_bytes`] corresponds to `Nucleus.CasPair.ofBlob`, the
/// projections correspond to `Nucleus.CasPair.hash` and
/// `Nucleus.CasPair.blob`, and the invariant is `Nucleus.CasPair.valid_hash`.
/// [`CasAssertion::check`] corresponds to `Nucleus.CasAssertion.check?`.
///
/// ```compile_fail
/// use bytes::Bytes;
/// use covalence_logic_cas::CasFact;
///
/// let assertion = CasFact::from_bytes(Bytes::new()).into_assertion();
/// let forged = CasFact { assertion };
/// ```
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasFact {
    assertion: CasAssertion,
}

impl CasFact {
    /// Checks a specific address and complete blob, then introduces a fact.
    ///
    /// # Errors
    ///
    /// Returns [`CasCheckError`] when `hash` is not the blob's address.
    pub fn new(hash: O256, blob: impl Into<Bytes>) -> Result<Self, CasCheckError> {
        CasAssertion::new(hash, blob).check()
    }

    /// Hashes the complete bytes and introduces a checked fact.
    ///
    /// `Bytes` is reference counted, so passing an existing [`Bytes`] value
    /// retains it without copying its contents.
    #[must_use]
    pub fn from_bytes(bytes: impl Into<Bytes>) -> Self {
        let blob = bytes.into();
        let hash = O256::from_bytes(&blob);
        Self {
            assertion: CasAssertion { hash, blob },
        }
    }

    /// Returns the hash of the complete blob.
    #[must_use]
    pub const fn hash(&self) -> O256 {
        self.assertion.hash
    }

    /// Borrows all bytes of the complete blob.
    #[must_use]
    pub const fn bytes(&self) -> &Bytes {
        &self.assertion.blob
    }

    pub(crate) const fn as_assertion(&self) -> &CasAssertion {
        &self.assertion
    }

    /// Forgets the checked invariant and returns the ordinary assertion.
    #[must_use]
    pub fn into_assertion(self) -> CasAssertion {
        self.assertion
    }
}

impl TryFrom<CasAssertion> for CasFact {
    type Error = CasCheckError;

    fn try_from(assertion: CasAssertion) -> Result<Self, Self::Error> {
        assertion.check()
    }
}
