//! Serde representation for Covalence object identifiers.

use std::str::FromStr;

use cid::{CidGeneric, Version, multihash::Multihash};
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};

use crate::{O256, Obj, blake3::Cov};

// Multicodec codes from the canonical multicodec table.
const RAW: u64 = 0x55;
const BLAKE3_256: u64 = 0x1e;

type O256Cid = CidGeneric<32>;

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DagJsonLink {
    #[serde(rename = "/")]
    cid: String,
}

impl Serialize for Obj<Cov> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let hash = Multihash::<32>::wrap(BLAKE3_256, self.as_ref())
            .expect("an O256 digest always fits in a 32-byte multihash");
        DagJsonLink {
            cid: O256Cid::new_v1(RAW, hash).to_string(),
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Obj<Cov> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let link = DagJsonLink::deserialize(deserializer)?;
        let cid = O256Cid::from_str(&link.cid).map_err(de::Error::custom)?;

        if link.cid != cid.to_string() {
            return Err(de::Error::custom(
                "O256 CID must use canonical lowercase base32",
            ));
        }
        if cid.version() != Version::V1 {
            return Err(de::Error::custom("O256 CID must use CIDv1"));
        }
        if cid.codec() != RAW {
            return Err(de::Error::custom("O256 CID must use the raw multicodec"));
        }
        if cid.hash().code() != BLAKE3_256 {
            return Err(de::Error::custom(
                "O256 CID must use the blake3-256 multihash code",
            ));
        }

        let bytes: [u8; 32] = cid
            .hash()
            .digest()
            .try_into()
            .map_err(|_| de::Error::custom("O256 CID digest must be 32 bytes"))?;
        Ok(O256::from_array(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn o256_round_trips_as_a_dag_json_link() {
        let value = O256::from_array([0xab; 32]);
        let json = serde_json::to_string(&value).unwrap();

        assert_eq!(
            json,
            r#"{"/":"bafkr4iflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"}"#
        );
        assert_eq!(serde_json::from_str::<O256>(&json).unwrap(), value);
    }

    #[test]
    fn o256_rejects_a_cid_from_another_namespace() {
        let json = r#"{"/":"bafkreiflvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvov2xk5lvm"}"#;
        let error = serde_json::from_str::<O256>(json).unwrap_err();

        assert!(error.to_string().contains("blake3-256"));
    }

    #[test]
    fn o256_rejects_non_link_json() {
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
