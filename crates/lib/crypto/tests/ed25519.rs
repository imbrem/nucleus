use covalence_lib_crypto::ed25519::{Signer, SigningKey, Verifier};

#[test]
fn reexport_signs_and_verifies() {
    let signing_key = SigningKey::from_bytes(&[7; 32]);
    let verifying_key = signing_key.verifying_key();
    let signature = signing_key.sign(b"trusted state");

    assert!(verifying_key.verify(b"trusted state", &signature).is_ok());
    assert!(
        verifying_key
            .verify(b"untrusted state", &signature)
            .is_err()
    );
}
