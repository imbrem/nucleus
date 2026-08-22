use crate::{Bytes, O256};

/// An unchecked claim that `blob` has the given content hash.
///
/// This is the runtime counterpart of Lean's `Nucleus.CasAssertion`. It is
/// ordinary data: constructing one does not establish
/// `Nucleus.CasAssertion.Valid`. Convert it to [`crate::CasFact`] to check the
/// claim.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CasAssertion {
    /// Claimed `O256` hash of the complete blob.
    pub hash: O256,
    /// Complete claimed blob.
    pub blob: Bytes,
}
