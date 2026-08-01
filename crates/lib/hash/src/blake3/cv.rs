//! Low-level operations over BLAKE3 trees.
//!
//! [`Blake3Mode`] is the explicit API for unkeyed, keyed, and context-keyed
//! trees. The convenience methods on [`Blake3Cv`] always use
//! [`Blake3Mode::Unkeyed`].

use blake3::hazmat::{self, HasherExt, Mode};

use crate::{Blake3Hash, CtxKey, Namespace, O256, Obj, Opaque};

/// Public BLAKE3 tree mode used to hash leaves and combine chaining values.
///
/// Keys are namespace material, not secrets carried by this type. All three
/// modes produce values in the same [`Blake3Hash`] namespace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Blake3Mode {
    /// Ordinary unkeyed BLAKE3.
    Unkeyed,
    /// BLAKE3 keyed hashing with a public 256-bit key.
    Keyed(O256),
    /// BLAKE3 derive-key material hashing with a prederived context key.
    ContextKeyed(CtxKey),
}

impl Blake3Mode {
    /// Hashes a complete byte string in this mode.
    #[must_use]
    pub fn hash(self, bytes: impl AsRef<[u8]>) -> Blake3Hash {
        let mut hasher = self.hasher();
        hasher.update(bytes.as_ref());
        Obj::from_array(*hasher.finalize().as_bytes())
    }

    /// Hashes a non-empty canonical subtree starting at `input_offset`.
    ///
    /// # Panics
    ///
    /// In accordance with BLAKE3's hazmat API, this panics for empty input, an
    /// offset that is not chunk-aligned, or input that exceeds the maximum
    /// subtree size permitted at its offset.
    #[must_use]
    pub fn subtree_cv(self, input_offset: u64, bytes: impl AsRef<[u8]>) -> Blake3Cv {
        let mut hasher = self.hasher();
        hasher.set_input_offset(input_offset);
        hasher.update(bytes.as_ref());
        Obj::from_array(hasher.finalize_non_root())
    }

    /// Combines two non-root child chaining values in this mode.
    #[must_use]
    pub fn merge(self, left: Blake3Cv, right: Blake3Cv) -> Blake3Cv {
        Obj::from_array(hazmat::merge_subtrees_non_root(
            left.as_bytes(),
            right.as_bytes(),
            self.hazmat(),
        ))
    }

    /// Combines the final child pair into a root digest in this mode.
    #[must_use]
    pub fn root(self, left: Blake3Cv, right: Blake3Cv) -> Blake3Hash {
        let hash = hazmat::merge_subtrees_root(left.as_bytes(), right.as_bytes(), self.hazmat());
        Obj::from_array(*hash.as_bytes())
    }

    fn hasher(self) -> blake3::Hasher {
        match self {
            Self::Unkeyed => blake3::Hasher::new(),
            Self::Keyed(key) => blake3::Hasher::new_keyed(key.as_bytes()),
            Self::ContextKeyed(key) => blake3::Hasher::new_from_context_key(key.as_bytes()),
        }
    }

    fn hazmat(&self) -> Mode<'_> {
        match self {
            Self::Unkeyed => Mode::Hash,
            Self::Keyed(key) => Mode::KeyedHash(key.as_bytes()),
            Self::ContextKeyed(key) => Mode::DeriveKeyMaterial(key.as_bytes()),
        }
    }
}

/// The namespace of non-root BLAKE3 Merkle-tree chaining values.
///
/// A value in this namespace is an untrusted intermediate hash. The type keeps
/// chaining values distinct from root digests, but does not prove that a value
/// occupies a valid position in a particular BLAKE3 tree.
pub struct Blake3Merkle;

impl Namespace for Blake3Merkle {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// A non-root BLAKE3 Merkle-tree chaining value.
pub type Blake3Cv = Obj<Blake3Merkle>;

impl Blake3Cv {
    /// Hashes a non-empty chunk or subtree in unkeyed BLAKE3 mode.
    ///
    /// The offset is measured in bytes from the start of the complete input.
    /// Use [`Blake3Mode::subtree_cv`] instead for keyed or context-keyed trees.
    ///
    /// # Panics
    ///
    /// In accordance with BLAKE3's hazmat API, this panics for empty input, an
    /// offset that is not chunk-aligned, or input that exceeds the maximum
    /// subtree size permitted at its offset.
    #[must_use]
    pub fn from_subtree(input_offset: u64, bytes: impl AsRef<[u8]>) -> Self {
        Blake3Mode::Unkeyed.subtree_cv(input_offset, bytes)
    }

    /// Combines two child chaining values in unkeyed BLAKE3 mode.
    ///
    /// The caller is responsible for supplying left and right children that
    /// occupy a valid position in the intended unkeyed BLAKE3 tree. Use
    /// [`Blake3Mode::merge`] instead for keyed or context-keyed trees.
    #[must_use]
    pub fn merge(self, right: Self) -> Self {
        Blake3Mode::Unkeyed.merge(self, right)
    }

    /// Combines the final child pair into an unkeyed BLAKE3 root digest.
    ///
    /// The caller is responsible for supplying the left and right children in
    /// the correct order and tree position. Use [`Blake3Mode::root`] instead
    /// for keyed or context-keyed trees.
    #[must_use]
    pub fn root(self, right: Self) -> Blake3Hash {
        Blake3Mode::Unkeyed.root(self, right)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtree_operations_reproduce_blake3_roots() {
        let chunk0 = [b'a'; blake3::CHUNK_LEN];
        let chunk1 = [b'b'; blake3::CHUNK_LEN];
        let chunk2 = [b'c'; 42];

        let cv0 = Blake3Cv::from_subtree(0, chunk0);
        let cv1 = Blake3Cv::from_subtree(blake3::CHUNK_LEN as u64, chunk1);
        let cv2 = Blake3Cv::from_subtree(2 * blake3::CHUNK_LEN as u64, chunk2);

        let mut input = Vec::new();
        input.extend_from_slice(&chunk0);
        input.extend_from_slice(&chunk1);
        assert_eq!(cv0.root(cv1), Blake3Hash::from_bytes(&input));

        input.extend_from_slice(&chunk2);
        assert_eq!(cv0.merge(cv1).root(cv2), Blake3Hash::from_bytes(input));
    }

    #[test]
    fn chaining_value_namespace_does_not_claim_structural_validity() {
        let representative = Blake3Merkle;
        assert_eq!(std::mem::size_of_val(&representative), 0);

        let arbitrary = Blake3Cv::from_array([0xa5; 32]);
        let root = arbitrary.root(arbitrary);
        assert_ne!(root, Blake3Hash::default());
    }
}
