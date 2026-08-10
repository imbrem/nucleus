use std::error::Error as StdError;
use std::fmt;

use covalence_lib_crypto::ed25519::VerifyingKey;
use covalence_lib_hash::O256;

use super::{
    Ed25519Verifier, VerificationError, Verifier as _, ed25519_key_id,
    schema_valid_snapshot_statement,
};

/// Untrusted bytes and a schema-qualified signature.
pub struct SignedSnapshotEnvelope {
    bytes: covalence_neutron::Bytes,
    attestation: SignedSnapshotAttestation,
}

/// Untrusted snapshot attestation that can be checked without its bytes.
pub struct SignedSnapshotAttestation {
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
            attestation: SignedSnapshotAttestation::new(
                schema, image, signer, public_key, signature,
            ),
        }
    }

    /// Verifies the image hash and schema-qualified signature.
    ///
    /// # Errors
    ///
    /// Returns an error for an image/key identity mismatch, invalid public-key encoding, malformed
    /// signature, or failed signature verification.
    pub fn authenticate(self) -> Result<AuthenticatedSnapshot, SnapshotAuthenticationError> {
        let actual_image = O256::from_bytes(&self.bytes);
        if actual_image != self.attestation.image {
            return Err(SnapshotAuthenticationError::ImageMismatch {
                claimed: self.attestation.image,
                actual: actual_image,
            });
        }
        let claim = self.attestation.authenticate()?;
        Ok(AuthenticatedSnapshot {
            bytes: self.bytes,
            claim,
        })
    }
}

impl SignedSnapshotAttestation {
    /// Copies one untrusted schema-qualified attestation into owned storage.
    #[must_use]
    pub fn new(
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Self {
        Self {
            schema,
            image,
            signer,
            public_key,
            signature: covalence_neutron::Bytes::copy_from_slice(signature),
        }
    }

    /// Verifies the signer identity and schema/image signature.
    ///
    /// # Errors
    ///
    /// Returns an error for a key-identity mismatch, invalid key encoding, malformed signature, or
    /// failed signature verification.
    pub fn authenticate(self) -> Result<AuthenticatedSnapshotClaim, SnapshotAuthenticationError> {
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
        Ok(AuthenticatedSnapshotClaim { attestation: self })
    }
}

/// An authenticated schema-qualified image claim.
pub struct AuthenticatedSnapshotClaim {
    attestation: SignedSnapshotAttestation,
}

impl AuthenticatedSnapshotClaim {
    /// Returns the authenticated claimed schema.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.attestation.schema
    }

    /// Returns the authenticated claimed image identity.
    #[must_use]
    pub const fn image(&self) -> O256 {
        self.attestation.image
    }

    /// Returns the authenticated signing-key identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.attestation.signer
    }

    /// Returns the public key which authenticated the claim.
    #[must_use]
    pub const fn public_key(&self) -> &[u8; 32] {
        &self.attestation.public_key
    }

    /// Returns the exact authenticated signature.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.attestation.signature
    }
}

/// Authenticated bytes and their schema-qualified claim.
pub struct AuthenticatedSnapshot {
    bytes: covalence_neutron::Bytes,
    claim: AuthenticatedSnapshotClaim,
}

impl AuthenticatedSnapshot {
    /// Returns the exact authenticated bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the independently authenticated hash-first claim.
    #[must_use]
    pub const fn claim(&self) -> &AuthenticatedSnapshotClaim {
        &self.claim
    }

    /// Discards the fetched bytes and retains only the authenticated hash-first claim.
    #[must_use]
    pub fn into_claim(self) -> AuthenticatedSnapshotClaim {
        self.claim
    }

    /// Returns the authenticated claimed schema.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.claim.schema()
    }

    /// Returns the authenticated exact image hash.
    #[must_use]
    pub const fn image(&self) -> O256 {
        self.claim.image()
    }

    /// Returns the authenticated signing-key identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.claim.signer()
    }

    /// Returns the public key which authenticated the claim.
    #[must_use]
    pub const fn public_key(&self) -> &[u8; 32] {
        self.claim.public_key()
    }

    /// Returns the exact authenticated signature.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        self.claim.signature()
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
    use covalence_lib_crypto::ed25519::SigningKey;

    use super::*;
    use crate::{Ed25519Signer, Signer as _};

    fn envelope() -> SignedSnapshotEnvelope {
        let bytes = b"exact database bytes";
        let schema = O256::from_bytes(b"example schema");
        let image = O256::from_bytes(bytes);
        let signer = Ed25519Signer::new(SigningKey::from_bytes(&[7; 32]));
        let signature = signer
            .sign(
                signer.key_id(),
                schema_valid_snapshot_statement(schema, image),
            )
            .unwrap();
        SignedSnapshotEnvelope::new(
            bytes,
            schema,
            image,
            signer.key_id(),
            signer.verifying_key().to_bytes(),
            &signature,
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
    fn authenticates_a_hash_first_claim_without_snapshot_bytes() {
        let valid = envelope().authenticate().unwrap();
        let claim = SignedSnapshotAttestation::new(
            valid.schema(),
            valid.image(),
            valid.signer(),
            *valid.public_key(),
            valid.signature(),
        )
        .authenticate()
        .unwrap();
        assert_eq!(claim.schema(), valid.schema());
        assert_eq!(claim.image(), valid.image());
        assert_eq!(claim.signer(), valid.signer());
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
