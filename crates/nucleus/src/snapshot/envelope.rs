use bytes::Bytes;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;

use crate::{
    Connection, DatabaseError, SignError, VerificationError, Verifier, valid_snapshot_statement,
};

const MAGIC: &[u8; 8] = b"NUCSNP\0\x01";
const EVIDENCE_MAGIC: &[u8; 8] = b"NUCEVD\0\x01";
const HEADER_LEN: usize = MAGIC.len() + 8 + 32 + 4;
const MAX_SIGNATURE_LEN: usize = 1024 * 1024;

/// A versioned, out-of-band signature over one exact Nucleus database image.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedSnapshot {
    image: Bytes,
    key: O256,
    signature: Bytes,
}

impl SignedSnapshot {
    /// Returns the exact serialized database image covered by the signature.
    #[must_use]
    pub const fn image(&self) -> &Bytes {
        &self.image
    }

    /// Returns the stable identity of the signing public key.
    #[must_use]
    pub const fn key(&self) -> O256 {
        self.key
    }

    /// Returns the signature bytes.
    #[must_use]
    pub const fn signature(&self) -> &Bytes {
        &self.signature
    }

    /// Returns the stable content hash of the covered image.
    #[must_use]
    pub fn snapshot_hash(&self) -> O256 {
        O256::from_bytes(&self.image)
    }

    /// Encodes the signed snapshot in the v1 binary envelope.
    ///
    /// # Errors
    ///
    /// Returns an error if the image or signature length cannot be represented,
    /// or the signature exceeds the format's defensive size limit.
    pub fn encode(&self) -> Result<Bytes, SnapshotError> {
        let image_len =
            u64::try_from(self.image.len()).map_err(|_| SnapshotError::ImageTooLarge)?;
        let signature_len =
            u32::try_from(self.signature.len()).map_err(|_| SnapshotError::SignatureTooLarge)?;
        if self.signature.len() > MAX_SIGNATURE_LEN {
            return Err(SnapshotError::SignatureTooLarge);
        }

        let capacity = HEADER_LEN
            .checked_add(self.image.len())
            .and_then(|length| length.checked_add(self.signature.len()))
            .ok_or(SnapshotError::ImageTooLarge)?;
        let mut encoded = Vec::with_capacity(capacity);
        encoded.extend_from_slice(MAGIC);
        encoded.extend_from_slice(&image_len.to_be_bytes());
        encoded.extend_from_slice(self.key.as_ref());
        encoded.extend_from_slice(&signature_len.to_be_bytes());
        encoded.extend_from_slice(&self.image);
        encoded.extend_from_slice(&self.signature);
        Ok(Bytes::from(encoded))
    }

    /// Decodes a signed snapshot from the v1 binary envelope.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed, truncated, oversized, or trailing
    /// representation.
    pub fn decode(encoded: &[u8]) -> Result<Self, SnapshotError> {
        if encoded.len() < HEADER_LEN || &encoded[..MAGIC.len()] != MAGIC {
            return Err(SnapshotError::MalformedEnvelope);
        }
        let mut cursor = MAGIC.len();
        let image_len = read_u64(encoded, &mut cursor)?;
        let image_len = usize::try_from(image_len).map_err(|_| SnapshotError::ImageTooLarge)?;
        let key = read_array::<32>(encoded, &mut cursor)?;
        let signature_len = read_u32(encoded, &mut cursor)?;
        let signature_len =
            usize::try_from(signature_len).map_err(|_| SnapshotError::SignatureTooLarge)?;
        if signature_len > MAX_SIGNATURE_LEN {
            return Err(SnapshotError::SignatureTooLarge);
        }
        let expected = HEADER_LEN
            .checked_add(image_len)
            .and_then(|length| length.checked_add(signature_len))
            .ok_or(SnapshotError::ImageTooLarge)?;
        if encoded.len() != expected {
            return Err(SnapshotError::MalformedEnvelope);
        }
        let image_end = cursor
            .checked_add(image_len)
            .ok_or(SnapshotError::ImageTooLarge)?;
        Ok(Self {
            image: Bytes::copy_from_slice(&encoded[cursor..image_end]),
            key: O256::from_array(key),
            signature: Bytes::copy_from_slice(&encoded[image_end..]),
        })
    }

    fn evidence(&self) -> Result<Bytes, SnapshotError> {
        let signature_len =
            u32::try_from(self.signature.len()).map_err(|_| SnapshotError::SignatureTooLarge)?;
        let mut evidence = Vec::with_capacity(EVIDENCE_MAGIC.len() + 32 + 4 + self.signature.len());
        evidence.extend_from_slice(EVIDENCE_MAGIC);
        evidence.extend_from_slice(self.key.as_ref());
        evidence.extend_from_slice(&signature_len.to_be_bytes());
        evidence.extend_from_slice(&self.signature);
        Ok(Bytes::from(evidence))
    }
}

impl Connection {
    /// Serializes and signs this connection's persistent Nucleus state.
    ///
    /// # Errors
    ///
    /// Returns an error when serialization or signing fails.
    pub fn sign_snapshot(&self, key: O256) -> Result<SignedSnapshot, SnapshotError> {
        let image = self
            .serialize()
            .map_err(|source| SnapshotError::Serialize { source })?;
        let snapshot_hash = self.cas().hash(&image);
        let signature = self
            .sign(key, valid_snapshot_statement(snapshot_hash))
            .map_err(|source| SnapshotError::Sign { source })?;
        Ok(SignedSnapshot {
            image,
            key,
            signature,
        })
    }

    /// Opens a signed image using one explicitly trusted verifier.
    ///
    /// Verification happens before `SQLite` parses the image. The returned
    /// connection records the accepted image and signature evidence in its
    /// default CAS and trusted-snapshot relation.
    ///
    /// # Errors
    ///
    /// Returns an error when verification, import, CAS storage, or trust
    /// recording fails.
    pub fn open_signed_snapshot(
        snapshot: &SignedSnapshot,
        verifier: Box<dyn Verifier>,
    ) -> Result<Self, SnapshotError> {
        let snapshot_hash = snapshot.snapshot_hash();
        verifier
            .verify(
                snapshot.key,
                valid_snapshot_statement(snapshot_hash),
                &snapshot.signature,
            )
            .map_err(|source| SnapshotError::Verify { source })?;

        let mut connection =
            Self::from_image(&snapshot.image).map_err(|source| SnapshotError::Import { source })?;
        connection
            .trust_verifier(snapshot.key, verifier)
            .map_err(|source| SnapshotError::Trust { source })?;
        let stored_image = connection
            .cas()
            .store(&snapshot.image)
            .map_err(|source| SnapshotError::Cas { source })?;
        if stored_image != snapshot_hash {
            return Err(SnapshotError::HashMismatch {
                expected: snapshot_hash,
                actual: stored_image,
            });
        }
        let evidence = connection
            .cas()
            .store(&snapshot.evidence()?)
            .map_err(|source| SnapshotError::Cas { source })?;
        connection
            .record_trusted_snapshot(
                covalence_neutron::TRUSTED_SNAPSHOTS,
                snapshot_hash,
                Some(evidence),
            )
            .map_err(|source| SnapshotError::Trust { source })?;
        Ok(connection)
    }
}

fn read_u64(encoded: &[u8], cursor: &mut usize) -> Result<u64, SnapshotError> {
    Ok(u64::from_be_bytes(read_array(encoded, cursor)?))
}

fn read_u32(encoded: &[u8], cursor: &mut usize) -> Result<u32, SnapshotError> {
    Ok(u32::from_be_bytes(read_array(encoded, cursor)?))
}

fn read_array<const N: usize>(
    encoded: &[u8],
    cursor: &mut usize,
) -> Result<[u8; N], SnapshotError> {
    let end = cursor
        .checked_add(N)
        .ok_or(SnapshotError::MalformedEnvelope)?;
    let bytes = encoded
        .get(*cursor..end)
        .ok_or(SnapshotError::MalformedEnvelope)?;
    *cursor = end;
    bytes
        .try_into()
        .map_err(|_| SnapshotError::MalformedEnvelope)
}

/// Failure to encode, sign, verify, or open a snapshot.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SnapshotError {
    /// The envelope is malformed or uses an unsupported version.
    #[snafu(display("malformed or unsupported signed snapshot envelope"))]
    MalformedEnvelope,

    /// The image is too large for the envelope representation.
    #[snafu(display("database image is too large for the snapshot envelope"))]
    ImageTooLarge,

    /// The signature exceeds the envelope's defensive size bound.
    #[snafu(display("signature is too large for the snapshot envelope"))]
    SignatureTooLarge,

    /// Persistent state could not be serialized.
    #[snafu(display("could not serialize snapshot: {source}"))]
    Serialize {
        /// Underlying serialization failure.
        source: covalence_neutron::ImageError,
    },

    /// The valid-snapshot statement could not be signed.
    #[snafu(display("could not sign snapshot: {source}"))]
    Sign {
        /// Underlying signer failure.
        source: SignError,
    },

    /// The snapshot signature was not accepted.
    #[snafu(display("snapshot signature was not accepted: {source}"))]
    Verify {
        /// Underlying verifier failure.
        source: VerificationError,
    },

    /// The verified database image is not valid Nucleus state.
    #[snafu(display("verified snapshot is not valid Nucleus state: {source}"))]
    Import {
        /// Underlying import failure.
        source: DatabaseError,
    },

    /// Snapshot or evidence bytes could not be recorded.
    #[snafu(display("could not record snapshot content: {source}"))]
    Cas {
        /// Underlying CAS failure.
        source: covalence_neutron::CasError,
    },

    /// CAS storage returned an address different from the verified image hash.
    #[snafu(display("snapshot CAS address is {actual}, expected {expected}"))]
    HashMismatch {
        /// Verified image hash.
        expected: O256,
        /// Unexpected CAS address.
        actual: O256,
    },

    /// Connection-local trust metadata could not be recorded.
    #[snafu(display("could not record snapshot trust: {source}"))]
    Trust {
        /// Underlying metadata failure.
        source: covalence_neutron::TrustMetadataError,
    },
}

#[cfg(test)]
mod tests {
    use covalence_lib_crypto::ed25519::SigningKey;

    use super::*;
    use crate::{AdditionFact, Ed25519Signer, Ed25519Verifier, Signer};

    fn signed_fixture() -> (SignedSnapshot, SigningKey) {
        let key = SigningKey::from_bytes(&[19; 32]);
        let signing_capability = Ed25519Signer::new(key.clone());
        let mut connection = Connection::create_in_memory().expect("create");
        let positive = connection
            .create_addition("positive")
            .expect("positive table");
        let negative = connection
            .create_addition("negative")
            .expect("negative table");
        positive
            .insert(AdditionFact::sum(20, 22).expect("fact"))
            .expect("insert");
        negative
            .insert(AdditionFact::sum(-20, -22).expect("fact"))
            .expect("insert");
        connection
            .cas()
            .store(b"connection-local CAS exercise")
            .expect("store CAS data");
        connection
            .register_signer(signing_capability.key_id(), Box::new(signing_capability))
            .expect("register signer");
        let signed = connection
            .sign_snapshot(crate::ed25519_key_id(key.verifying_key().as_bytes()))
            .expect("sign snapshot");
        (signed, key)
    }

    #[test]
    fn envelope_round_trips_and_opens_multiple_addition_tables() {
        let (signed, key) = signed_fixture();
        let encoded = signed.encode().expect("encode");
        let decoded = SignedSnapshot::decode(&encoded).expect("decode");
        assert_eq!(decoded, signed);

        let connection = Connection::open_signed_snapshot(
            &decoded,
            Box::new(Ed25519Verifier::new(key.verifying_key())),
        )
        .expect("open signed snapshot");
        assert_eq!(connection.additions().expect("validate").len(), 2);
        assert_eq!(
            connection
                .cas()
                .fetch(decoded.snapshot_hash())
                .expect("fetch")
                .as_deref(),
            Some(decoded.image().as_ref())
        );
        assert!(
            connection
                .snapshot_is_trusted(
                    covalence_neutron::TRUSTED_SNAPSHOTS,
                    decoded.snapshot_hash()
                )
                .expect("query trust")
        );
    }

    #[test]
    fn rejects_image_signature_and_key_tampering() {
        let (signed, key) = signed_fixture();

        let mut modified_image_bytes = signed.image.to_vec();
        modified_image_bytes[100] ^= 1;
        let modified_image = SignedSnapshot {
            image: Bytes::from(modified_image_bytes),
            ..signed.clone()
        };
        assert_verify_error(&modified_image, &key);

        let mut modified_signature_bytes = signed.signature.to_vec();
        modified_signature_bytes[0] ^= 1;
        let modified_signature = SignedSnapshot {
            signature: Bytes::from(modified_signature_bytes),
            ..signed.clone()
        };
        assert_verify_error(&modified_signature, &key);

        assert!(matches!(
            Connection::open_signed_snapshot(
                &signed,
                Box::new(Ed25519Verifier::new(
                    SigningKey::from_bytes(&[20; 32]).verifying_key()
                ))
            ),
            Err(SnapshotError::Verify { .. })
        ));
    }

    #[test]
    fn rejects_malformed_and_oversized_framing() {
        let (signed, _) = signed_fixture();
        let encoded = signed.encode().expect("encode");
        for prefix_len in [0, 1, MAGIC.len(), HEADER_LEN - 1, encoded.len() - 1] {
            assert!(matches!(
                SignedSnapshot::decode(&encoded[..prefix_len]),
                Err(SnapshotError::MalformedEnvelope)
            ));
        }

        let mut wrong_magic = encoded.to_vec();
        wrong_magic[0] ^= 1;
        assert!(matches!(
            SignedSnapshot::decode(&wrong_magic),
            Err(SnapshotError::MalformedEnvelope)
        ));

        let mut trailing = encoded.to_vec();
        trailing.extend_from_slice(b"trailing");
        assert!(matches!(
            SignedSnapshot::decode(&trailing),
            Err(SnapshotError::MalformedEnvelope)
        ));

        let mut oversized_signature = encoded.to_vec();
        oversized_signature[48..52].copy_from_slice(
            &u32::try_from(MAX_SIGNATURE_LEN + 1)
                .expect("fits")
                .to_be_bytes(),
        );
        assert!(matches!(
            SignedSnapshot::decode(&oversized_signature),
            Err(SnapshotError::SignatureTooLarge)
        ));
    }

    #[test]
    fn valid_signature_does_not_bypass_relation_validation() {
        let key = SigningKey::from_bytes(&[31; 32]);
        let signing_capability = Ed25519Signer::new(key.clone());
        let neutron = covalence_neutron::Connection::open_in_memory().expect("open");
        neutron
            .sqlite()
            .execute_batch(
                "CREATE TABLE cov_catalog (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT, WITHOUT ROWID;
                CREATE TABLE hostile (
                    tm INTEGER NOT NULL,
                    lhs INTEGER NOT NULL,
                    rhs INTEGER NOT NULL,
                    PRIMARY KEY (tm, lhs, rhs)
                ) STRICT, WITHOUT ROWID;
                INSERT INTO hostile VALUES (4, 2, 3);
                INSERT INTO cov_catalog VALUES ('hostile', 'cov.addition/v0');",
            )
            .expect("construct hostile image");
        let image = neutron.serialize().expect("serialize");
        let snapshot_hash = O256::from_bytes(&image);
        let signature = signing_capability
            .sign(
                signing_capability.key_id(),
                valid_snapshot_statement(snapshot_hash),
            )
            .expect("sign invalid state");
        let signed = SignedSnapshot {
            image,
            key: signing_capability.key_id(),
            signature,
        };

        assert!(matches!(
            Connection::open_signed_snapshot(
                &signed,
                Box::new(Ed25519Verifier::new(key.verifying_key()))
            ),
            Err(SnapshotError::Import { .. })
        ));
    }

    fn assert_verify_error(snapshot: &SignedSnapshot, key: &SigningKey) {
        assert!(matches!(
            Connection::open_signed_snapshot(
                snapshot,
                Box::new(Ed25519Verifier::new(key.verifying_key()))
            ),
            Err(SnapshotError::Verify { .. })
        ));
    }
}
