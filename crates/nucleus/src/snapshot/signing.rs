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
