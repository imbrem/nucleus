use covalence_lib_hash::{O256, o256};

/// Assertion that a persistent `SQLite` image is valid Nucleus state under v0.
///
/// Signing [`valid_snapshot_statement`] attests that the exact image named by
/// its hash has a truthful catalog and truthful interpreted relations. This
/// assertion never includes connection-local `cov_conn_*` state.
pub const COV_VALID_DB_V0: O256 =
    o256!("e8095bfb2c053a7ae2033105d9b194160cb55d36b02330aaf9b787262aa58078");

/// Namespace root for Ed25519 public-key identities.
pub const ED25519_PUBLIC_KEY_V0: O256 =
    o256!("6d5b0cc7de272425ce91d2712182758b08fec18eb9c2ce3c37457dfdf9ee5822");

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
