//! Cryptographic primitives used by Nucleus.
//!
//! Currently this crate is a small Ed25519 façade.

/// Ed25519 signing and verification.
///
/// ```
/// use covalence_lib_crypto::ed25519::{Signer, SigningKey, Verifier};
///
/// let signing_key = SigningKey::from_bytes(&[7; 32]);
/// let message = b"trusted state";
/// let signature = signing_key.sign(message);
///
/// signing_key.verifying_key().verify(message, &signature)?;
/// # Ok::<(), covalence_lib_crypto::ed25519::SignatureError>(())
/// ```
pub use ed25519_dalek as ed25519;
