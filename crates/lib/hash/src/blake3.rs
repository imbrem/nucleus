//! BLAKE3 namespace and hashing operations.

use crate::Namespace;

#[cfg(feature = "blake3")]
use crate::{O256, Obj};

/// The namespace containing BLAKE3 root hashes.
pub enum Blake3 {}

impl Namespace<32> for Blake3 {}

#[cfg(feature = "blake3")]
impl Blake3 {
    /// Computes a BLAKE3 hash in the BLAKE3 namespace.
    #[must_use]
    pub fn hash(bytes: impl AsRef<[u8]>) -> Obj<32, Self> {
        Obj::from_bytes(*::blake3::hash(bytes.as_ref()).as_bytes())
    }

    /// Computes a BLAKE3 hash from a reader in the BLAKE3 namespace.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn hash_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Obj<32, Self>> {
        let mut hasher = ::blake3::Hasher::new();
        std::io::copy(&mut reader, &mut hasher)?;
        Ok(Obj::from_bytes(*hasher.finalize().as_bytes()))
    }

    /// Computes a keyed BLAKE3 hash in the BLAKE3 namespace.
    #[must_use]
    pub fn keyed(key: O256, bytes: impl AsRef<[u8]>) -> Obj<32, Self> {
        Obj::from_bytes(*::blake3::keyed_hash(key.as_bytes(), bytes.as_ref()).as_bytes())
    }

    /// Computes a keyed BLAKE3 hash from a reader in the BLAKE3 namespace.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn keyed_from_reader(
        key: O256,
        mut reader: impl std::io::Read,
    ) -> std::io::Result<Obj<32, Self>> {
        let mut hasher = ::blake3::Hasher::new_keyed(key.as_bytes());
        std::io::copy(&mut reader, &mut hasher)?;
        Ok(Obj::from_bytes(*hasher.finalize().as_bytes()))
    }
}

#[cfg(feature = "blake3")]
impl O256 {
    /// Computes an opaque BLAKE3 hash.
    #[must_use]
    pub fn blake3(bytes: impl AsRef<[u8]>) -> Self {
        Blake3::hash(bytes).opaque()
    }

    /// Computes an opaque BLAKE3 hash from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn blake3_from_reader(reader: impl std::io::Read) -> std::io::Result<Self> {
        Blake3::hash_from_reader(reader).map(Obj::opaque)
    }

    /// Computes an opaque keyed BLAKE3 hash.
    #[must_use]
    pub fn blake3_keyed(key: O256, bytes: impl AsRef<[u8]>) -> Self {
        Blake3::keyed(key, bytes).opaque()
    }

    /// Computes an opaque keyed BLAKE3 hash from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn blake3_keyed_from_reader(
        key: O256,
        reader: impl std::io::Read,
    ) -> std::io::Result<Self> {
        Blake3::keyed_from_reader(key, reader).map(Obj::opaque)
    }
}

#[cfg(all(test, feature = "blake3"))]
mod tests {
    use std::io::Cursor;

    use super::*;

    #[test]
    fn keyed_opaque_and_namespaced_apis_match_blake3() {
        let key = O256::from_bytes([42; ::blake3::KEY_LEN]);
        let expected = ::blake3::keyed_hash(key.as_bytes(), b"hello");

        assert_eq!(
            O256::blake3_keyed(key, b"hello").as_bytes(),
            expected.as_bytes()
        );
        assert_eq!(Blake3::keyed(key, b"hello").as_bytes(), expected.as_bytes());
        assert_eq!(
            O256::blake3_keyed_from_reader(key, Cursor::new(b"hello"))
                .expect("opaque reader")
                .as_bytes(),
            expected.as_bytes()
        );
        assert_eq!(
            Blake3::keyed_from_reader(key, Cursor::new(b"hello"))
                .expect("namespaced reader")
                .as_bytes(),
            expected.as_bytes()
        );
    }
}
