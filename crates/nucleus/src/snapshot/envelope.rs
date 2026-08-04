use std::error::Error as StdError;
use std::fmt;

use covalence_lib_crypto::ed25519::VerifyingKey;
use covalence_lib_hash::O256;

use super::{
    Ed25519Verifier, VerificationError, Verifier as _, ed25519_key_id,
    schema_valid_snapshot_statement,
};

/// Untrusted wire envelope for exact bytes and one schema-qualified signature.
///
/// The constructor deliberately performs no cryptographic, database, schema, or trust checks.
pub struct SignedSnapshotEnvelope {
    bytes: covalence_neutron::Bytes,
    schema: O256,
    image: O256,
    signer: O256,
    public_key: [u8; 32],
    signature: covalence_neutron::Bytes,
}

impl SignedSnapshotEnvelope {
    /// Copies one untrusted received envelope into owned storage.
    #[must_use]
    pub fn new(
        bytes: &[u8],
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Self {
        Self {
            bytes: covalence_neutron::Bytes::copy_from_slice(bytes),
            schema,
            image,
            signer,
            public_key,
            signature: covalence_neutron::Bytes::copy_from_slice(signature),
        }
    }

    /// Authenticates internal envelope coherence and the schema-qualified signature.
    ///
    /// Success means only that the included public key signed the exact `(schema, image)` claim.
    /// It does not trust that key, parse the bytes, validate the schema, or establish the claim's
    /// truth.
    ///
    /// # Errors
    ///
    /// Returns an error for an image/key identity mismatch, invalid public-key encoding, malformed
    /// signature, or failed signature verification.
    pub fn authenticate(self) -> Result<AuthenticatedSnapshot, SnapshotAuthenticationError> {
        let actual_image = O256::from_bytes(&self.bytes);
        if actual_image != self.image {
            return Err(SnapshotAuthenticationError::ImageMismatch {
                claimed: self.image,
                actual: actual_image,
            });
        }
        let actual_signer = ed25519_key_id(&self.public_key);
        if actual_signer != self.signer {
            return Err(SnapshotAuthenticationError::SignerMismatch {
                claimed: self.signer,
                actual: actual_signer,
            });
        }
        let verifying_key = VerifyingKey::from_bytes(&self.public_key)
            .map_err(|_| SnapshotAuthenticationError::InvalidPublicKey(self.signer))?;
        Ed25519Verifier::new(verifying_key)
            .verify(
                self.signer,
                schema_valid_snapshot_statement(self.schema, self.image),
                &self.signature,
            )
            .map_err(SnapshotAuthenticationError::Signature)?;
        Ok(AuthenticatedSnapshot { envelope: self })
    }
}

/// Evidence that one included public key authenticated an exact schema-qualified snapshot claim.
///
/// This is cryptographic evidence, not database validation or a trust decision.
pub struct AuthenticatedSnapshot {
    envelope: SignedSnapshotEnvelope,
}

impl AuthenticatedSnapshot {
    /// Returns the exact authenticated bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.envelope.bytes
    }

    /// Returns the authenticated claimed schema.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.envelope.schema
    }

    /// Returns the authenticated exact image hash.
    #[must_use]
    pub const fn image(&self) -> O256 {
        self.envelope.image
    }

    /// Returns the authenticated signing-key identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.envelope.signer
    }

    /// Returns the public key which authenticated the claim.
    #[must_use]
    pub const fn public_key(&self) -> &[u8; 32] {
        &self.envelope.public_key
    }

    /// Returns the exact authenticated signature.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.envelope.signature
    }
}

/// Failure to authenticate one received schema-qualified snapshot envelope.
#[derive(Debug)]
pub enum SnapshotAuthenticationError {
    /// The bytes do not hash to the claimed image identity.
    ImageMismatch { claimed: O256, actual: O256 },
    /// The public key does not derive the claimed signer identity.
    SignerMismatch { claimed: O256, actual: O256 },
    /// The fixed-width public-key bytes are not a valid Ed25519 key encoding.
    InvalidPublicKey(O256),
    /// Signature parsing or verification failed.
    Signature(VerificationError),
}

impl fmt::Display for SnapshotAuthenticationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ImageMismatch { claimed, actual } => {
                write!(
                    formatter,
                    "snapshot image mismatch: claimed {claimed}, actual {actual}"
                )
            }
            Self::SignerMismatch { claimed, actual } => {
                write!(
                    formatter,
                    "snapshot signer mismatch: claimed {claimed}, actual {actual}"
                )
            }
            Self::InvalidPublicKey(signer) => {
                write!(
                    formatter,
                    "snapshot signer {signer} has an invalid Ed25519 public key"
                )
            }
            Self::Signature(error) => error.fmt(formatter),
        }
    }
}

impl StdError for SnapshotAuthenticationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Signature(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AllowAll, Kernel};

    fn envelope() -> SignedSnapshotEnvelope {
        let kernel = Kernel::ephemeral();
        let mut connection = kernel.open_hol(AllowAll).unwrap();
        let snapshot = kernel.export_hol(&mut connection).unwrap();
        let attestation = snapshot.attestation();
        SignedSnapshotEnvelope::new(
            snapshot.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
    }

    #[test]
    fn authenticates_one_self_contained_schema_qualified_envelope() {
        let authenticated = envelope().authenticate().unwrap();
        assert_eq!(
            O256::from_bytes(authenticated.bytes()),
            authenticated.image()
        );
        assert_eq!(
            ed25519_key_id(authenticated.public_key()),
            authenticated.signer()
        );
        assert_eq!(authenticated.signature().len(), 64);
    }

    #[test]
    fn independently_rejects_wrong_bytes_schema_signer_and_signature() {
        let valid = envelope().authenticate().unwrap();
        let wrong_bytes = SignedSnapshotEnvelope::new(
            b"other bytes",
            valid.schema(),
            valid.image(),
            valid.signer(),
            *valid.public_key(),
            valid.signature(),
        );
        assert!(matches!(
            wrong_bytes.authenticate(),
            Err(SnapshotAuthenticationError::ImageMismatch { .. })
        ));
        let wrong_schema = SignedSnapshotEnvelope::new(
            valid.bytes(),
            O256::from_bytes(b"wrong schema"),
            valid.image(),
            valid.signer(),
            *valid.public_key(),
            valid.signature(),
        );
        assert!(matches!(
            wrong_schema.authenticate(),
            Err(SnapshotAuthenticationError::Signature(_))
        ));
        let wrong_signer = SignedSnapshotEnvelope::new(
            valid.bytes(),
            valid.schema(),
            valid.image(),
            O256::from_bytes(b"wrong signer"),
            *valid.public_key(),
            valid.signature(),
        );
        assert!(matches!(
            wrong_signer.authenticate(),
            Err(SnapshotAuthenticationError::SignerMismatch { .. })
        ));
        let wrong_signature = SignedSnapshotEnvelope::new(
            valid.bytes(),
            valid.schema(),
            valid.image(),
            valid.signer(),
            *valid.public_key(),
            &[0; 64],
        );
        assert!(matches!(
            wrong_signature.authenticate(),
            Err(SnapshotAuthenticationError::Signature(_))
        ));
    }
}
