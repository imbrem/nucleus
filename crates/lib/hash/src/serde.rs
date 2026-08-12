//! Serde representations for Covalence object identifiers and hashes.

use std::str::FromStr;

use cid::{CidGeneric, Version, multihash::Multihash};
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};

use crate::{Blake3, Cov, Git, Namespace, Obj, Sha256};

// Codes from the canonical multicodec table.
const RAW: u64 = 0x55;
const GIT_RAW: u64 = 0x78;
const SHA1: u64 = 0x11;
const SHA2_256: u64 = 0x12;
const BLAKE3_256: u64 = 0x1e;

type HashCid = CidGeneric<32>;

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DagJsonLink {
    #[serde(rename = "/")]
    cid: String,
}

fn serialize<N, S>(
    value: &Obj<N>,
    codec: u64,
    hash_code: u64,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    N: Namespace,
    S: Serializer,
{
    let hash = Multihash::<32>::wrap(hash_code, value.as_ref())
        .expect("supported hash representations fit in a 32-byte multihash");
    DagJsonLink {
        cid: HashCid::new_v1(codec, hash).to_string(),
    }
    .serialize(serializer)
}

fn deserialize<'de, N, D>(
    deserializer: D,
    name: &str,
    codec: u64,
    hash_code: u64,
) -> Result<Obj<N>, D::Error>
where
    N: Namespace,
    D: Deserializer<'de>,
{
    let link = DagJsonLink::deserialize(deserializer)?;
    let cid = HashCid::from_str(&link.cid).map_err(de::Error::custom)?;

    if link.cid != cid.to_string() {
        return Err(de::Error::custom(format_args!(
            "{name} CID must use canonical lowercase base32"
        )));
    }
    if cid.version() != Version::V1 {
        return Err(de::Error::custom(format_args!("{name} CID must use CIDv1")));
    }
    if cid.codec() != codec {
        return Err(de::Error::custom(format_args!(
            "{name} CID has the wrong multicodec"
        )));
    }
    if cid.hash().code() != hash_code {
        return Err(de::Error::custom(format_args!(
            "{name} CID has the wrong multihash code"
        )));
    }

    let mut bytes = N::Bytes::default();
    if cid.hash().digest().len() != N::BYTES {
        return Err(de::Error::custom(format_args!(
            "{name} CID digest must be {} bytes",
            N::BYTES
        )));
    }
    bytes.as_mut().copy_from_slice(cid.hash().digest());
    Ok(Obj::from_array(bytes))
}

macro_rules! impl_serde {
    ($namespace:ty, $name:literal, $codec:expr, $hash:expr) => {
        impl Serialize for Obj<$namespace> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serialize(self, $codec, $hash, serializer)
            }
        }

        impl<'de> Deserialize<'de> for Obj<$namespace> {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserialize(deserializer, $name, $codec, $hash)
            }
        }
    };
}

impl_serde!(Cov, "O256", RAW, BLAKE3_256);
impl_serde!(Blake3, "Blake3Hash", RAW, BLAKE3_256);
impl_serde!(Sha256, "Sha256Hash", RAW, SHA2_256);
impl_serde!(Git, "GitHash", GIT_RAW, SHA1);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Blake3Hash, GitHash, O256, Sha256Hash};

    fn assert_round_trip<T>(value: T, expected: &str)
    where
        T: Copy + std::fmt::Debug + Eq + Serialize + for<'de> Deserialize<'de>,
    {
        let json = serde_json::to_string(&value).unwrap();
        assert_eq!(json, expected);
        assert_eq!(serde_json::from_str::<T>(&json).unwrap(), value);
    }

    #[test]
    fn hashes_round_trip_as_dag_json_links() {
        assert_round_trip(
            O256::from_array([0xab; 32]),
            r#"{"/":"bafkr4iflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"}"#,
        );
        assert_round_trip(
            Blake3Hash::from_array([0xab; 32]),
            r#"{"/":"bafkr4iflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"}"#,
        );
        assert_round_trip(
            Sha256Hash::from_array([0xab; 32]),
            r#"{"/":"bafkreiflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"}"#,
        );
        assert_round_trip(
            GitHash::from_array([0xab; 20]),
            r#"{"/":"baf4bcfflvov2xk5lvov2xk5lvov2xk5lvov2xky"}"#,
        );
    }

    #[test]
    fn namespaces_are_not_interchangeable() {
        let sha256 = serde_json::to_string(&Sha256Hash::from_array([0xab; 32])).unwrap();
        assert!(serde_json::from_str::<O256>(&sha256).is_err());

        let git = serde_json::to_string(&GitHash::from_array([0xab; 20])).unwrap();
        assert!(serde_json::from_str::<Blake3Hash>(&git).is_err());
    }

    #[test]
    fn malformed_or_noncanonical_links_are_rejected() {
        assert!(serde_json::from_str::<O256>(r#""abab""#).is_err());
        assert!(serde_json::from_str::<O256>(r#"{"/":"not a cid"}"#).is_err());
        assert!(
            serde_json::from_str::<O256>(
                r#"{"/":"bafkr4iflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm","extra":true}"#,
            )
            .is_err()
        );
    }
}
