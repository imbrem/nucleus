//! Low-level operations over the unkeyed BLAKE3 tree.

use blake3::hazmat::{self, HasherExt, Mode};

use crate::{Blake3, Blake3Hash, Namespace, Obj, Opaque};

/// The namespace of non-root BLAKE3 Merkle-tree chaining values.
///
/// A value in this namespace is an untrusted intermediate hash. The type keeps
/// chaining values distinct from root digests, but does not prove that a value
/// occupies a valid position in a particular BLAKE3 tree.
#[derive(Clone, Copy)]
pub struct Blake3Merkle;

impl Namespace for Blake3Merkle {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// A non-root BLAKE3 Merkle-tree chaining value.
pub type Blake3Cv = Obj<Blake3Merkle>;

impl Blake3Cv {
    /// Hashes a non-empty chunk or subtree starting at `input_offset`.
    ///
    /// The offset is measured in bytes from the start of the complete input.
    ///
    /// # Panics
    ///
    /// In accordance with BLAKE3's hazmat API, this panics for empty input, an
    /// offset that is not chunk-aligned, or input that exceeds the maximum
    /// subtree size permitted at its offset.
    #[must_use]
    pub fn from_subtree(input_offset: u64, bytes: impl AsRef<[u8]>) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.set_input_offset(input_offset);
        hasher.update(bytes.as_ref());
        Self::from_array(hasher.finalize_non_root())
    }

    /// Combines two child chaining values into a non-root parent.
    ///
    /// The caller is responsible for supplying left and right children that
    /// occupy a valid position in the intended BLAKE3 tree.
    #[must_use]
    pub fn merge(self, right: Self) -> Self {
        Self::from_array(hazmat::merge_subtrees_non_root(
            self.as_bytes(),
            right.as_bytes(),
            Mode::Hash,
        ))
    }

    /// Combines the final pair of child chaining values into a root digest.
    ///
    /// The caller is responsible for supplying the left and right children in
    /// the correct order and tree position.
    #[must_use]
    pub fn root(self, right: Self) -> Blake3Hash {
        let hash = hazmat::merge_subtrees_root(self.as_bytes(), right.as_bytes(), Mode::Hash);
        Obj::<Blake3>::from_array(*hash.as_bytes())
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
