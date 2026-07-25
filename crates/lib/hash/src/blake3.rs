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
}
