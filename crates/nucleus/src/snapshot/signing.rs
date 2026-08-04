use std::{error::Error, fmt};

use bytes::Bytes;
use covalence_lib_crypto::ed25519::{
    Signature as Ed25519Signature, Signer as _, SigningKey, Verifier as _, VerifyingKey,
};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;

use super::ed25519_key_id;

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
    use super::*;
    use crate::{schema_valid_snapshot_statement, valid_snapshot_statement};

    fn signing_key() -> SigningKey {
        SigningKey::from_bytes(&[7; 32])
    }

    #[test]
    fn trait_objects_sign_and_verify_statements() {
        let key = signing_key();
        let key_id = ed25519_key_id(key.verifying_key().as_bytes());
        let signer: Box<dyn Signer> = Box::new(Ed25519Signer::new(key.clone()));
        let verifier: Box<dyn Verifier> = Box::new(Ed25519Verifier::new(key.verifying_key()));
        let statement = valid_snapshot_statement(O256::from_bytes(b"database image"));

        let signature = signer.sign(key_id, statement).expect("sign");
        verifier
            .verify(key_id, statement, &signature)
            .expect("verify");
        assert!(matches!(
            verifier.verify(
                key_id,
                valid_snapshot_statement(O256::default()),
                &signature
            ),
            Err(VerificationError::InvalidSignature { .. })
        ));
    }

    #[test]
    fn capabilities_reject_wrong_keys_and_malformed_signatures() {
        let key = signing_key();
        let signer = Ed25519Signer::new(key.clone());
        let verifier = Ed25519Verifier::new(key.verifying_key());
        let statement = O256::from_bytes(b"statement");
        let wrong_key = O256::from_bytes(b"wrong key");

        assert!(matches!(
            signer.sign(wrong_key, statement),
            Err(SignError::UnknownKey { .. })
        ));
        assert!(matches!(
            verifier.verify(wrong_key, statement, &[0; 64]),
            Err(VerificationError::UnknownKey { .. })
        ));
        assert!(matches!(
            verifier.verify(verifier.key_id(), statement, &[0; 63]),
            Err(VerificationError::MalformedSignature { .. })
        ));
    }

    #[test]
    fn schema_qualification_is_part_of_the_signed_statement() {
        let key = signing_key();
        let signer = Ed25519Signer::new(key.clone());
        let verifier = Ed25519Verifier::new(key.verifying_key());
        let image = O256::from_bytes(b"same database image");
        let schema = O256::from_bytes(b"HOL schema v3");
        let statement = schema_valid_snapshot_statement(schema, image);
        let signature = signer.sign(signer.key_id(), statement).unwrap();
        verifier
            .verify(verifier.key_id(), statement, &signature)
            .unwrap();
        let wrong_schema =
            schema_valid_snapshot_statement(O256::from_bytes(b"other schema"), image);
        assert!(matches!(
            verifier.verify(verifier.key_id(), wrong_schema, &signature),
            Err(VerificationError::InvalidSignature { .. })
        ));
    }
}
