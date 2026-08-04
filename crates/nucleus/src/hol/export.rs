use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;

use super::{Hol, Operation, Policy, ValidatedHolImage};
use crate::{Connection, Kernel, SignError, Signer as _, schema_valid_snapshot_statement};

/// Out-of-band authentication of exact HOL database bytes under one schema.
pub struct HolSnapshotAttestation {
    schema: O256,
    image: O256,
    signer: O256,
    signature: covalence_neutron::Bytes,
}

impl HolSnapshotAttestation {
    /// Returns the exact physical schema named by the signature.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.schema
    }

    /// Returns the content hash of the signed bytes.
    #[must_use]
    pub const fn image(&self) -> O256 {
        self.image
    }

    /// Returns the signing public-key identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.signer
    }

    /// Returns the out-of-band signature bytes.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.signature
    }
}

/// Complete in-memory bytes plus their kernel attestation.
pub struct SignedHolSnapshot {
    image: ValidatedHolImage,
    attestation: HolSnapshotAttestation,
}

impl SignedHolSnapshot {
    /// Returns the detached structural validation evidence and exact bytes.
    #[must_use]
    pub const fn image(&self) -> &ValidatedHolImage {
        &self.image
    }

    /// Returns the schema-qualified kernel signature.
    #[must_use]
    pub const fn attestation(&self) -> &HolSnapshotAttestation {
        &self.attestation
    }
}

/// Failure to serialize and sign local authoritative HOL state.
#[derive(Debug)]
pub enum HolExportError {
    /// The connection policy denied export.
    Denied(Operation),
    /// The main database could not be serialized.
    Image(covalence_neutron::ImageError),
    /// The serialized bytes failed self-validation under their exact schema.
    Validation(super::HolImageValidationError),
    /// The kernel signing capability failed.
    Sign(SignError),
}

impl fmt::Display for HolExportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::Image(error) => error.fmt(formatter),
            Self::Validation(error) => error.fmt(formatter),
            Self::Sign(error) => error.fmt(formatter),
        }
    }
}

impl StdError for HolExportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Denied(_) => None,
            Self::Image(error) => Some(error),
            Self::Validation(error) => Some(error),
            Self::Sign(error) => Some(error),
        }
    }
}

impl<P: Policy> Connection<Hol<P>> {
    fn validated_export_image(&mut self) -> Result<ValidatedHolImage, HolExportError> {
        let (neutron, hol) = self.parts_mut();
        if !hol.policy.allows(Operation::ExportSignedSnapshot) {
            return Err(HolExportError::Denied(Operation::ExportSignedSnapshot));
        }
        let schema = hol.schema.clone();
        let bytes = neutron.serialize().map_err(HolExportError::Image)?;
        ValidatedHolImage::validate_with_schema(&bytes, &schema).map_err(HolExportError::Validation)
    }
}

impl Kernel {
    /// Serializes local authoritative HOL state and signs its schema and hash.
    ///
    /// A live [`super::ProofSession`] holds the required mutable connection
    /// borrow, so only capabilities explicitly persisted before the session
    /// ends can reach this boundary.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies export, serialization/self-validation
    /// fails, or the kernel signing capability rejects the statement.
    pub fn export_hol<P: Policy>(
        &self,
        connection: &mut Connection<Hol<P>>,
    ) -> Result<SignedHolSnapshot, HolExportError> {
        let image = connection.validated_export_image()?;
        let schema = image.schema();
        let image_hash = image.hash();
        let signer = self.key_id();
        let signature = self
            .signer()
            .sign(signer, schema_valid_snapshot_statement(schema, image_hash))
            .map_err(HolExportError::Sign)?;
        Ok(SignedHolSnapshot {
            image,
            attestation: HolSnapshotAttestation {
                schema,
                image: image_hash,
                signer,
                signature,
            },
        })
    }
}
