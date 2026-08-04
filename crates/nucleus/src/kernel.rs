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
}
