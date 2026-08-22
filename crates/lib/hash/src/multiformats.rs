//! Explicit multihash and CID conversions for object identifiers.

use cid::{CidGeneric, multihash::Multihash};
use covalence_lib_error::snafu::{self, Snafu};

use crate::{Blake3, Cov, CtxKeyNamespace, Git, Namespace, Obj, Sha1, Sha256};

const RAW: u64 = 0x55;
const SHA1: u64 = 0x11;
const SHA2_256: u64 = 0x12;
const BLAKE3_256: u64 = 0x1e;

/// A multihash or CID does not describe the requested object namespace.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum InvalidMultiformat {
    /// The multihash names a hash function other than the namespace's.
    #[snafu(display("expected multihash code {expected:#x}, found {actual:#x}"))]
    MultihashCode {
        /// Code this namespace uses.
        expected: u64,
        /// Code carried by the input.
        actual: u64,
    },
    /// The digest is not as wide as the namespace's identifiers.
    #[snafu(display("expected a {expected}-byte digest, found {actual}"))]
    DigestLength {
        /// Width this namespace uses.
        expected: usize,
        /// Width carried by the input.
        actual: usize,
    },
    /// The CID names a codec other than raw.
    #[snafu(display("expected CID codec {expected:#x}, found {actual:#x}"))]
    CidCodec {
        /// The only codec these identifiers use.
        expected: u64,
        /// Codec carried by the input.
        actual: u64,
    },
}

/// A namespace with a standard multihash code.
///
/// Implementations must use a byte representation no wider than 32 bytes.
pub trait MultiformatNamespace: Namespace {
    /// The multicodec code used to identify this namespace's hash algorithm.
    const MULTIHASH_CODE: u64;
}

impl MultiformatNamespace for Cov {
    const MULTIHASH_CODE: u64 = BLAKE3_256;
}

impl MultiformatNamespace for Blake3 {
    const MULTIHASH_CODE: u64 = BLAKE3_256;
}

impl MultiformatNamespace for Sha256 {
    const MULTIHASH_CODE: u64 = SHA2_256;
}

impl MultiformatNamespace for CtxKeyNamespace {
    const MULTIHASH_CODE: u64 = BLAKE3_256;
}

impl MultiformatNamespace for Sha1 {
    const MULTIHASH_CODE: u64 = SHA1;
}

impl MultiformatNamespace for Git {
    const MULTIHASH_CODE: u64 = SHA1;
}

impl<N: MultiformatNamespace> Obj<N> {
    /// Wraps this identifier in its standard multihash representation.
    ///
    /// # Panics
    ///
    /// Panics if `N` violates [`MultiformatNamespace`]'s 32-byte width requirement.
    #[must_use]
    pub fn to_multihash(self) -> Multihash<32> {
        Multihash::wrap(N::MULTIHASH_CODE, self.as_ref())
            .expect("standard object identifiers fit in a 32-byte multihash")
    }

    /// Extracts an identifier from its standard multihash representation.
    ///
    /// # Errors
    ///
    /// Returns an error when the code or digest width does not match this namespace.
    pub fn from_multihash(hash: &Multihash<32>) -> Result<Self, InvalidMultiformat> {
        if hash.code() != N::MULTIHASH_CODE {
            return Err(InvalidMultiformat::MultihashCode {
                expected: N::MULTIHASH_CODE,
                actual: hash.code(),
            });
        }
        if hash.digest().len() != N::BYTES {
            return Err(InvalidMultiformat::DigestLength {
                expected: N::BYTES,
                actual: hash.digest().len(),
            });
        }
        let mut bytes = N::Bytes::default();
        bytes.as_mut().copy_from_slice(hash.digest());
        Ok(Obj::from_array(bytes))
    }

    /// Wraps this identifier in a raw `CIDv1`.
    #[must_use]
    pub fn to_raw_cid(self) -> CidGeneric<32> {
        CidGeneric::new_v1(RAW, self.to_multihash())
    }

    /// Extracts an identifier from a raw CID using its standard multihash.
    ///
    /// # Errors
    ///
    /// Returns an error when the codec, hash code, or digest width does not match.
    pub fn from_raw_cid(cid: &CidGeneric<32>) -> Result<Self, InvalidMultiformat> {
        if cid.codec() != RAW {
            return Err(InvalidMultiformat::CidCodec {
                expected: RAW,
                actual: cid.codec(),
            });
        }
        Self::from_multihash(cid.hash())
    }
}

#[cfg(test)]
mod tests {
    use crate::{GitHash, O256};

    #[test]
    fn standard_multiformats_round_trip() {
        let value = O256::from_array([0xab; 32]);
        assert_eq!(O256::from_multihash(&value.to_multihash()), Ok(value));
        assert_eq!(O256::from_raw_cid(&value.to_raw_cid()), Ok(value));
        assert_eq!(
            value.to_raw_cid().to_string(),
            "bafkr4iflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"
        );
    }

    #[test]
    fn namespace_mismatches_are_rejected() {
        let git = GitHash::from_array([0xab; 20]);
        assert!(O256::from_multihash(&git.to_multihash()).is_err());
        assert!(O256::from_raw_cid(&git.to_raw_cid()).is_err());
    }
}
