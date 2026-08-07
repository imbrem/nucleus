use covalence_lib_hash::{O256, o256_path};

mod signing;

pub use signing::{Ed25519Signer, Ed25519Verifier, SignError, Signer, VerificationError, Verifier};

/// Assertion that a persistent `SQLite` image is valid Nucleus state under v0.
///
/// Signing [`valid_snapshot_statement`] attests that the exact image named by
/// its hash has a truthful catalog and truthful interpreted relations. This
/// assertion never includes connection-local `cov_conn_*` state.
pub const COV_VALID_DB_V0: O256 = o256_path!(
    ::nucleus.snapshot.valid.v0 =
        "e8095bfb2c053a7ae2033105d9b194160cb55d36b02330aaf9b787262aa58078"
);

/// Namespace root for Ed25519 public-key identities.
pub const ED25519_PUBLIC_KEY_V0: O256 = o256_path!(
    ::crypto.public_key.ed25519.v0 =
        "6d5b0cc7de272425ce91d2712182758b08fec18eb9c2ce3c37457dfdf9ee5822"
);

/// Derives the standard object identity of an Ed25519 public key.
#[must_use]
pub fn ed25519_key_id(public_key: &[u8; 32]) -> O256 {
    ED25519_PUBLIC_KEY_V0.tag(public_key)
}

/// Derives the statement signed to attest a serialized database image.
#[must_use]
pub fn valid_snapshot_statement(snapshot_hash: O256) -> O256 {
    COV_VALID_DB_V0.tag(snapshot_hash)
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;

    use super::*;

    #[test]
    fn key_and_statement_vectors_are_stable() {
        assert_eq!(
            ed25519_key_id(&[7; 32]),
            O256::from_hex("6ec15cbe98f0347f4bef435ec2fb3f7b2779a3f54a038b4c523413ccac5436af")
                .expect("valid key ID vector")
        );
        assert_eq!(
            valid_snapshot_statement(O256::from_bytes(b"sample image")),
            O256::from_hex("c4325090ba3cf6ec5389b421d4cf324b8a7476583b1d10a84d365bdcd33b6a54")
                .expect("valid statement vector")
        );
    }
}
