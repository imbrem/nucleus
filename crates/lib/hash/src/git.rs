//! SHA-1 and traditional Git object namespaces.

use crate::{Namespace, Obj, Opaque};

#[cfg(feature = "git-sha1")]
use crate::HashNamespace;

/// Raw SHA-1 digests.
pub struct Sha1;

impl Namespace for Sha1 {
    const BYTES: usize = 20;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<20>;
}

/// Traditional Git SHA-1 object names.
///
/// Git names are content-derived and deliberately cannot be generated from
/// randomness.
///
/// ```compile_fail
/// use covalence_lib_hash::{Git, RandomNamespace};
/// fn assert_random<N: RandomNamespace>() {}
/// assert_random::<Git>();
/// ```
pub struct Git;

impl Namespace for Git {
    const BYTES: usize = 20;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<20>;
}

/// A traditional Git object name.
///
/// With the default `serde` feature, values use a DAG-JSON link containing a
/// `CIDv1` with the `git-raw` codec and `sha1` multihash code.
pub type GitHash = Obj<Git>;

#[cfg(feature = "git-sha1")]
impl HashNamespace for Sha1 {
    fn hash(bytes: impl AsRef<[u8]>) -> Obj<Self> {
        use sha1::Digest;
        Obj::from_array(sha1::Sha1::digest(bytes.as_ref()).into())
    }

    fn hash_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        use sha1::Digest;

        let mut hasher = sha1::Sha1::new();
        std::io::copy(&mut reader, &mut hasher)?;
        Ok(Obj::from_array(hasher.finalize().into()))
    }
}

impl Obj<Sha1> {
    /// Reinterprets a raw SHA-1 digest as a Git name.
    #[must_use]
    pub const fn into_git(self) -> GitHash {
        self.coerce()
    }
}

impl GitHash {
    /// Reinterprets a Git name as its raw SHA-1 digest.
    #[must_use]
    pub const fn into_sha1(self) -> Obj<Sha1> {
        self.coerce()
    }
}

/// Computes a raw SHA-1 digest.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn sha1(bytes: impl AsRef<[u8]>) -> Obj<Sha1> {
    Sha1::hash(bytes)
}

/// Computes a framed Git object name.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_object(object_type: &str, bytes: impl AsRef<[u8]>) -> GitHash {
    use sha1::Digest;

    let bytes = bytes.as_ref();
    let mut hasher = sha1::Sha1::new();
    hasher.update(object_type.as_bytes());
    hasher.update(b" ");
    hasher.update(bytes.len().to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(bytes);
    Obj::from_array(hasher.finalize().into())
}

/// Computes a Git blob name.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_blob(bytes: impl AsRef<[u8]>) -> GitHash {
    git_object("blob", bytes)
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "git-sha1")]
    use super::Sha1;
    #[cfg(feature = "git-sha1")]
    use crate::HashNamespace;

    #[cfg(feature = "git-sha1")]
    #[test]
    fn git_vectors_and_conversion() {
        assert_eq!(
            super::git_blob([]).to_string(),
            "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
        );
        assert_eq!(
            super::git_blob(b"hello").to_string(),
            "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0"
        );
        assert_ne!(
            super::git_blob(b"hello").as_bytes(),
            super::sha1(b"hello").as_bytes()
        );
        assert_eq!(
            super::git_blob(b"hello").into_sha1().into_git(),
            super::git_blob(b"hello")
        );
        assert_ne!(
            super::git_object("blob", b"hello"),
            super::git_object("tree", b"hello")
        );
        assert_eq!(
            Sha1::hash_from_reader(std::io::Cursor::new(b"hello")).unwrap(),
            super::sha1(b"hello")
        );
    }

    #[cfg(feature = "git-sha1")]
    #[test]
    fn sha1_reader_errors_are_preserved() {
        struct Failing;
        impl std::io::Read for Failing {
            fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("expected failure"))
            }
        }

        assert_eq!(
            Sha1::hash_from_reader(Failing)
                .expect_err("reader must fail")
                .kind(),
            std::io::ErrorKind::Other
        );
    }
}
