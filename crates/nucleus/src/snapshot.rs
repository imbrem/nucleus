use covalence_lib_hash::{O256, o256};

mod envelope;
mod signing;

pub use envelope::{
    AuthenticatedSnapshot, AuthenticatedSnapshotClaim, SignedSnapshotAttestation,
    SignedSnapshotEnvelope, SnapshotAuthenticationError,
};
pub use signing::{Ed25519Signer, Ed25519Verifier, SignError, Signer, VerificationError, Verifier};

/// Assertion that exact database bytes are valid under one explicit schema.
pub const COV_SCHEMA_VALID_DB_V0: O256 =
    o256!("c8ab229155a5fce29ba2b05f0fcedc2d9509f98997e2382d856d88cb23180fc1");

/// Namespace root for Ed25519 public-key identities.
pub const ED25519_PUBLIC_KEY_V0: O256 =
    o256!("6d5b0cc7de272425ce91d2712182758b08fec18eb9c2ce3c37457dfdf9ee5822");

/// Derives the standard object identity of an Ed25519 public key.
#[must_use]
pub fn ed25519_key_id(public_key: &[u8; 32]) -> O256 {
    ED25519_PUBLIC_KEY_V0.tag(public_key)
}

/// Derives the statement signed to attest exact bytes under an explicit schema.
#[must_use]
pub fn schema_valid_snapshot_statement(schema: O256, snapshot_hash: O256) -> O256 {
    let mut pair = [0_u8; 64];
    pair[..32].copy_from_slice(schema.as_ref());
    pair[32..].copy_from_slice(snapshot_hash.as_ref());
    COV_SCHEMA_VALID_DB_V0.tag(pair)
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::{O256, assert_o256_path};

    use super::*;

    #[test]
    fn protocol_roots_match_their_documented_paths() {
        assert_o256_path!(COV_SCHEMA_VALID_DB_V0, ::nucleus.snapshot.schema_valid.v0);
        assert_o256_path!(ED25519_PUBLIC_KEY_V0, ::crypto.public_key.ed25519.v0);
    }

    #[test]
    fn key_and_statement_vectors_are_stable() {
        assert_eq!(
            ed25519_key_id(&[7; 32]),
            O256::from_hex("6ec15cbe98f0347f4bef435ec2fb3f7b2779a3f54a038b4c523413ccac5436af")
                .expect("valid key ID vector")
        );
        assert_eq!(
            schema_valid_snapshot_statement(
                O256::from_bytes(b"sample schema"),
                O256::from_bytes(b"sample image"),
            ),
            O256::from_hex("f6e593334c605ece1bb19996bc45817162008d7219983e26560284396678797e")
                .expect("valid schema-qualified statement vector")
        );
    }
}
