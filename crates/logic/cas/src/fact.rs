use covalence_lib_error::snafu::Snafu;

use crate::{Bytes, CasAssertion, O256};

/// An unchecked whole-object assertion whose claimed hash is incorrect.
///
/// This is the failed branch of Lean's `Nucleus.CasAssertion.check?`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("claimed hash {claimed} does not match computed hash {computed}"))]
pub struct InvalidCasAssertion {
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
/// Conversion from [`CasAssertion`] corresponds to
/// `Nucleus.CasAssertion.check?`.
///
/// ```compile_fail
/// use bytes::Bytes;
/// use covalence_logic_cas::CasFact;
///
/// let assertion = CasFact::from_bytes(Bytes::new()).into_assertion();
/// let forged = CasFact { assertion };
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CasFact {
    assertion: CasAssertion,
}

impl CasFact {
    /// Hashes the complete bytes and introduces a checked fact.
    ///
    /// `Bytes` is reference counted, so passing an existing [`Bytes`] value
    /// retains it without copying its contents.
    #[must_use]
    pub fn from_bytes(bytes: impl Into<Bytes>) -> Self {
        let blob = bytes.into();
        let hash = O256::from_bytes(&blob);
        Self::from_valid(CasAssertion { hash, blob })
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

    /// Forgets the checked invariant and returns the ordinary assertion.
    #[must_use]
    pub fn into_assertion(self) -> CasAssertion {
        self.assertion
    }

    /// The sole unchecked representation constructor.
    ///
    /// Every caller in this module has either computed `assertion.hash` from
    /// the complete blob or compared that computation with the claimed hash.
    const fn from_valid(assertion: CasAssertion) -> Self {
        Self { assertion }
    }
}

impl TryFrom<CasAssertion> for CasFact {
    type Error = InvalidCasAssertion;

    fn try_from(assertion: CasAssertion) -> Result<Self, Self::Error> {
        let computed = O256::from_bytes(&assertion.blob);
        if computed == assertion.hash {
            Ok(Self::from_valid(assertion))
        } else {
            Err(InvalidCasAssertion {
                claimed: assertion.hash,
                computed,
            })
        }
    }
}

impl From<CasFact> for CasAssertion {
    fn from(fact: CasFact) -> Self {
        fact.into_assertion()
    }
}

impl From<&CasFact> for CasAssertion {
    fn from(fact: &CasFact) -> Self {
        fact.assertion.clone()
    }
}
