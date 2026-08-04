use covalence_lib_crypto::ed25519::{SigningKey, VerifyingKey};

use crate::{Connection, Hol, HolOpenError, Policy, Sql};

/// One kernel instance and its ephemeral signing identity.
///
/// The secret key is never persisted by this type. Higher layers may record
/// the public key in connection directories and use the signer for explicitly
/// authenticated inter-kernel protocols.
pub struct Kernel {
    signer: crate::Ed25519Signer,
}

impl Kernel {
    /// Creates a fresh kernel identity from host cryptographic randomness.
    #[must_use]
    pub fn ephemeral() -> Self {
        let secret = covalence_lib_rand::random::<[u8; 32]>();
        Self {
            signer: crate::Ed25519Signer::new(SigningKey::from_bytes(&secret)),
        }
    }

    /// Returns this kernel's public verification key.
    #[must_use]
    pub fn verifying_key(&self) -> VerifyingKey {
        self.signer.verifying_key()
    }

    /// Returns the content-derived identity of the public key.
    #[must_use]
    pub const fn key_id(&self) -> covalence_lib_hash::O256 {
        self.signer.key_id()
    }

    /// Returns this kernel's signing capability.
    #[must_use]
    pub const fn signer(&self) -> &crate::Ed25519Signer {
        &self.signer
    }

    /// Opens an unrestricted local SQL connection owned by this kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot open the in-memory database.
    pub fn open_sql(&self) -> Result<Connection<Sql>, covalence_neutron::ConnectionError> {
        Connection::<Sql>::open_in_memory()
    }

    /// Opens a policy-enclosed HOL connection owned by this kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the in-memory database or HOL schema cannot open.
    pub fn open_hol<P: Policy>(&self, policy: P) -> Result<Connection<Hol<P>>, HolOpenError> {
        Connection::open_hol_in_memory(policy)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AllowAll, ContextId, Verifier as _, schema_valid_snapshot_statement};

    struct DenyExport;

    impl crate::Policy for DenyExport {
        fn allows(&mut self, operation: crate::Operation) -> bool {
            operation != crate::Operation::ExportSignedSnapshot
        }
    }

    #[test]
    fn kernel_identities_are_independent_within_one_process() {
        let first = Kernel::ephemeral();
        let second = Kernel::ephemeral();
        assert_ne!(first.key_id(), second.key_id());
        assert_ne!(
            first.verifying_key().as_bytes(),
            second.verifying_key().as_bytes()
        );
    }

    #[test]
    fn signed_hol_export_contains_only_explicitly_persisted_authority() {
        let kernel = Kernel::ephemeral();
        let mut connection = kernel.open_hol(AllowAll).unwrap();
        let term = connection.insert_bool_term(false).unwrap();
        let context = connection.define_context([term]).unwrap();
        connection
            .with_proof_session(|mut proof| proof.prove_hypothesis(context, term).map(|_| ()))
            .unwrap();

        let first = kernel.export_hol(&mut connection).unwrap();
        assert_eq!(first.image().counts().untrusted_judgement_rows, 0);
        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, term)?;
                proof.persist_theorem(&theorem)
            })
            .unwrap();
        let second = kernel.export_hol(&mut connection).unwrap();
        assert_eq!(second.image().counts().untrusted_judgement_rows, 1);
        assert_ne!(first.attestation().image(), second.attestation().image());
        let verifier = crate::Ed25519Verifier::new(kernel.verifying_key());
        let attestation = second.attestation();
        verifier
            .verify(
                attestation.signer(),
                schema_valid_snapshot_statement(attestation.schema(), attestation.image()),
                attestation.signature(),
            )
            .unwrap();
        assert!(
            connection
                .proved_judgement(ContextId::from_i64(context.get()), term)
                .unwrap()
        );
    }

    #[test]
    fn signed_hol_export_is_policy_gated() {
        let kernel = Kernel::ephemeral();
        let mut connection = kernel.open_hol(DenyExport).unwrap();
        assert!(matches!(
            kernel.export_hol(&mut connection),
            Err(crate::HolExportError::Denied(
                crate::Operation::ExportSignedSnapshot
            ))
        ));
    }
}
