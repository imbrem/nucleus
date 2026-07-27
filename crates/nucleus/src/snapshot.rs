use std::{error::Error, fmt};

use bytes::Bytes;
use covalence_lib_crypto::ed25519::{
    Signature as Ed25519Signature, Signer as _, SigningKey, Verifier as _, VerifyingKey,
};
use covalence_lib_error::snafu::Snafu;
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

/// Object-safe capability for signing an O256 statement with a named key.
pub trait Signer: fmt::Debug {
    /// Signs `statement` with `key`.
    ///
    /// # Errors
    ///
    /// Returns an error when the signer does not hold `key` or signing fails.
    fn sign(&self, key: O256, statement: O256) -> Result<Bytes, SignError>;
}

/// Object-safe capability for verifying an O256 statement with a named key.
pub trait Verifier: fmt::Debug {
    /// Verifies `signature` over `statement` with `key`.
    ///
    /// # Errors
    ///
    /// Returns an error when the verifier does not represent `key`, the
    /// signature encoding is malformed, or verification fails.
    fn verify(&self, key: O256, statement: O256, signature: &[u8])
    -> Result<(), VerificationError>;
}

/// Failure to use a signing capability.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu), module)]
pub enum SignError {
    /// The signer does not hold the requested key.
    #[snafu(display("signer does not hold key {key}"))]
    UnknownKey {
        /// Requested public-key identity.
        key: O256,
    },

    /// The signing backend failed.
    #[snafu(display("signing with key {key} failed: {source}"))]
    Backend {
        /// Requested public-key identity.
        key: O256,
        /// Backend failure.
        source: Box<dyn Error + Send + Sync>,
    },
}

/// Failure to use a verification capability.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu), module)]
pub enum VerificationError {
    /// The verifier does not represent the requested key.
    #[snafu(display("verifier does not represent key {key}"))]
    UnknownKey {
        /// Requested public-key identity.
        key: O256,
    },

    /// The signature has the wrong encoding or length.
    #[snafu(display("signature for key {key} is malformed"))]
    MalformedSignature {
        /// Requested public-key identity.
        key: O256,
    },

    /// The signature is not valid for the statement.
    #[snafu(display("signature by key {key} is invalid"))]
    InvalidSignature {
        /// Requested public-key identity.
        key: O256,
    },
}

/// In-process Ed25519 signing capability.
#[derive(Debug)]
pub struct Ed25519Signer {
    signing_key: SigningKey,
    key_id: O256,
}

impl Ed25519Signer {
    /// Wraps one Ed25519 signing key.
    #[must_use]
    pub fn new(signing_key: SigningKey) -> Self {
        let key_id = ed25519_key_id(signing_key.verifying_key().as_bytes());
        Self {
            signing_key,
            key_id,
        }
    }

    /// Returns the public-key identity served by this signer.
    #[must_use]
    pub const fn key_id(&self) -> O256 {
        self.key_id
    }

    /// Returns the corresponding public verification key.
    #[must_use]
    pub fn verifying_key(&self) -> VerifyingKey {
        self.signing_key.verifying_key()
    }
}

impl Signer for Ed25519Signer {
    fn sign(&self, key: O256, statement: O256) -> Result<Bytes, SignError> {
        if key != self.key_id {
            return Err(SignError::UnknownKey { key });
        }
        let signature = self.signing_key.sign(statement.as_ref());
        Ok(Bytes::copy_from_slice(&signature.to_bytes()))
    }
}

/// In-process Ed25519 verification capability.
#[derive(Debug)]
pub struct Ed25519Verifier {
    verifying_key: VerifyingKey,
    key_id: O256,
}

impl Ed25519Verifier {
    /// Wraps one Ed25519 verification key.
    #[must_use]
    pub fn new(verifying_key: VerifyingKey) -> Self {
        let key_id = ed25519_key_id(verifying_key.as_bytes());
        Self {
            verifying_key,
            key_id,
        }
    }

    /// Returns the public-key identity served by this verifier.
    #[must_use]
    pub const fn key_id(&self) -> O256 {
        self.key_id
    }
}

impl Verifier for Ed25519Verifier {
    fn verify(
        &self,
        key: O256,
        statement: O256,
        signature: &[u8],
    ) -> Result<(), VerificationError> {
        if key != self.key_id {
            return Err(VerificationError::UnknownKey { key });
        }
        let signature = Ed25519Signature::try_from(signature)
            .map_err(|_| VerificationError::MalformedSignature { key })?;
        self.verifying_key
            .verify(statement.as_ref(), &signature)
            .map_err(|_| VerificationError::InvalidSignature { key })
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::{O256, assert_o256_path};

    use super::*;

    #[test]
    fn protocol_roots_match_their_documented_paths() {
        assert_o256_path!(COV_VALID_DB_V0, ::nucleus.snapshot.valid.v0);
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
            valid_snapshot_statement(O256::from_bytes(b"sample image")),
            O256::from_hex("c4325090ba3cf6ec5389b421d4cf324b8a7476583b1d10a84d365bdcd33b6a54")
                .expect("valid statement vector")
        );
    }

    #[test]
    fn trait_objects_sign_and_verify_statements() {
        let signer: Box<dyn Signer> =
            Box::new(Ed25519Signer::new(SigningKey::from_bytes(&[7; 32])));
        let key = ed25519_key_id(&signer_key().verifying_key().to_bytes());
        let verifier: Box<dyn Verifier> =
            Box::new(Ed25519Verifier::new(signer_key().verifying_key()));
        let statement = valid_snapshot_statement(O256::from_bytes(b"database image"));

        let signature = signer.sign(key, statement).expect("sign");
        verifier.verify(key, statement, &signature).expect("verify");
        assert!(matches!(
            verifier.verify(key, valid_snapshot_statement(O256::default()), &signature),
            Err(VerificationError::InvalidSignature { .. })
        ));
    }

    fn signer_key() -> SigningKey {
        SigningKey::from_bytes(&[7; 32])
    }
}
