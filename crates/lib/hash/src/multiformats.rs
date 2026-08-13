//! Explicit multihash and CID conversions for object identifiers.

use std::fmt;

use cid::{CidGeneric, multihash::Multihash};

use crate::{Blake3, Cov, CtxKeyNamespace, Git, Namespace, Obj, Sha1, Sha256};

const RAW: u64 = 0x55;
const SHA1: u64 = 0x11;
const SHA2_256: u64 = 0x12;
const BLAKE3_256: u64 = 0x1e;

/// A multihash large enough for every standard object identifier.
pub type HashMultihash = Multihash<32>;

/// A CID whose digest is at most 32 bytes.
pub type HashCid = CidGeneric<32>;

/// A multihash or CID does not describe the requested object namespace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidMultiformat(&'static str);

impl fmt::Display for InvalidMultiformat {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.0)
    }
}

impl std::error::Error for InvalidMultiformat {}

fn from_multihash<N: Namespace>(
    hash: &HashMultihash,
    code: u64,
) -> Result<Obj<N>, InvalidMultiformat> {
    if hash.code() != code {
        return Err(InvalidMultiformat("wrong multihash code"));
    }
    if hash.digest().len() != N::BYTES {
        return Err(InvalidMultiformat("wrong multihash digest length"));
    }
    let mut bytes = N::Bytes::default();
    bytes.as_mut().copy_from_slice(hash.digest());
    Ok(Obj::from_array(bytes))
}

macro_rules! impl_multiformats {
    ($namespace:ty, $hash:expr) => {
        impl Obj<$namespace> {
            /// Wraps this identifier in its standard multihash representation.
            #[must_use]
            pub fn to_multihash(self) -> HashMultihash {
                HashMultihash::wrap($hash, self.as_ref())
                    .expect("standard object identifiers fit in a 32-byte multihash")
            }

            /// Extracts an identifier from its standard multihash representation.
            ///
            /// # Errors
            ///
            /// Returns an error when the code or digest width does not match this namespace.
            pub fn from_multihash(hash: &HashMultihash) -> Result<Self, InvalidMultiformat> {
                from_multihash(hash, $hash)
            }

            /// Wraps this identifier in a `CIDv1` using its standard codec.
            #[must_use]
            pub fn to_raw_cid(self) -> HashCid {
                HashCid::new_v1(RAW, self.to_multihash())
            }

            /// Extracts an identifier from a CID using its standard codec and multihash.
            ///
            /// # Errors
            ///
            /// Returns an error when the codec, hash code, or digest width does not match.
            pub fn from_raw_cid(cid: &HashCid) -> Result<Self, InvalidMultiformat> {
                if cid.codec() != RAW {
                    return Err(InvalidMultiformat("wrong CID codec"));
                }
                Self::from_multihash(cid.hash())
            }
        }
    };
}

impl_multiformats!(Cov, BLAKE3_256);
impl_multiformats!(Blake3, BLAKE3_256);
impl_multiformats!(Sha256, SHA2_256);
impl_multiformats!(CtxKeyNamespace, BLAKE3_256);
impl_multiformats!(Sha1, SHA1);
impl_multiformats!(Git, SHA1);

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
