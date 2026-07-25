//! Raw SHA-1 and traditional Git object-name operations.

use crate::{Namespace, Obj};

/// The namespace containing raw SHA-1 digests.
pub enum Sha1 {}

impl Namespace<20> for Sha1 {}

/// The namespace containing traditional Git SHA-1 object names.
pub enum GitObject {}

impl Namespace<20> for GitObject {}

/// A traditional 160-bit Git object name.
pub type GitHash = Obj<20, GitObject>;

impl Obj<20, Sha1> {
    /// Interprets the raw SHA-1 bytes as a Git object name without validation.
    #[must_use]
    pub const fn into_git_object(self) -> GitHash {
        self.coerce()
    }
}

impl GitHash {
    /// Exposes a Git object name as its underlying raw SHA-1 digest.
    #[must_use]
    pub const fn into_sha1(self) -> Obj<20, Sha1> {
        self.coerce()
    }
}

/// Computes the raw SHA-1 digest of `bytes`.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_raw_sha1(bytes: impl AsRef<[u8]>) -> Obj<20, Sha1> {
    use sha1::Digest;
    Obj::from_bytes(sha1::Sha1::digest(bytes.as_ref()).into())
}

/// Computes a Git SHA-1 object name using `object_type` framing.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_object_sha1(object_type: &str, bytes: impl AsRef<[u8]>) -> GitHash {
    use sha1::Digest;

    let bytes = bytes.as_ref();
    let mut hasher = sha1::Sha1::new();
    hasher.update(object_type.as_bytes());
    hasher.update(b" ");
    hasher.update(bytes.len().to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(bytes);
    Obj::from_bytes(hasher.finalize().into())
}

/// Computes a Git blob object name.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_blob_sha1(bytes: impl AsRef<[u8]>) -> GitHash {
    git_object_sha1("blob", bytes)
}
