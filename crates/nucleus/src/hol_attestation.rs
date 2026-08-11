use std::{collections::BTreeMap, error::Error, fmt};

use covalence_kernel_hol::{CheckError, Theorem, Tree, check_closed};
use covalence_lib_hash::{COV_ROOT, O256};
use covalence_lib_serde::{Deserialize, Serialize};

use crate::{SignError, Signer, VerificationError, Verifier};

/// Experimental direct-tree JSON codec version in the signed judgement.
pub const CLOSED_THEOREM_JSON_VERSION: u32 = 0;

/// Derives the signed statement asserting `[] |- payload : bool`.
///
/// The domain commits to the experimental tree-JSON codec and empty hypothesis,
/// free-variable, and bound-variable contexts. It is deliberately distinct
/// from the valid-snapshot signature domain.
#[must_use]
pub fn closed_theorem_json_statement(payload_hash: O256) -> O256 {
    COV_ROOT
        .tag("nucleus")
        .tag("hol")
        .tag("closed_theorem")
        .tag("json")
        .tag("v0")
        .tag(payload_hash)
}

/// Detached signature over exact JSON bytes for a closed theorem conclusion.
///
/// This wire type is untrusted. Numeric byte arrays are intentionally used in
/// v0 so ordinary derived Serde is sufficient; a later codec may add explicit
/// hex/base64 wrappers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct SignedClosedTheorem {
    /// Experimental codec version.
    pub version: u32,
    /// Exact direct-tree JSON bytes. Whitespace changes require a new signature.
    pub payload: Vec<u8>,
    /// Hash of the exact payload bytes.
    pub payload_hash: [u8; 32],
    /// Signing-key identity.
    pub signer: [u8; 32],
    /// Detached signature bytes.
    pub signature: Vec<u8>,
}

/// Failure to serialize or sign a locally derived theorem.
#[derive(Debug)]
pub enum ExportError {
    /// Direct-tree JSON serialization failed.
    Json(covalence_lib_json::Error),
    /// The selected signing capability failed.
    Sign(SignError),
}

impl fmt::Display for ExportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Json(error) => write!(formatter, "could not serialize theorem: {error}"),
            Self::Sign(error) => write!(formatter, "could not sign theorem: {error}"),
        }
    }
}

impl Error for ExportError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Json(error) => Some(error),
            Self::Sign(error) => Some(error),
        }
    }
}

/// Signs the exact JSON conclusion of an already-derived closed theorem.
///
/// This function accepts theorem authority, never an arbitrary term. It does
/// not serialize a proof.
///
/// # Errors
///
/// Returns an error if JSON serialization or the signing capability fails.
pub fn sign_closed_theorem(
    theorem: &Theorem,
    signer: &dyn Signer,
    key: O256,
) -> Result<SignedClosedTheorem, ExportError> {
    let payload = covalence_lib_json::to_vec(theorem.conclusion()).map_err(ExportError::Json)?;
    let payload_hash = O256::from_bytes(&payload);
    let statement = closed_theorem_json_statement(payload_hash);
    let signature = signer
        .sign(key, statement)
        .map_err(ExportError::Sign)?
        .to_vec();
    Ok(SignedClosedTheorem {
        version: CLOSED_THEOREM_JSON_VERSION,
        payload,
        payload_hash: payload_hash.into_bytes(),
        signer: key.into_bytes(),
        signature,
    })
}

/// Failure to authenticate, trust, parse, or check an imported theorem.
#[derive(Debug)]
pub enum ImportError {
    /// The artifact names an unsupported experimental codec.
    UnsupportedVersion(u32),
    /// Exact payload bytes do not match the claimed hash.
    PayloadHashMismatch,
    /// No explicitly trusted verifier was registered for this signer.
    UntrustedSigner(O256),
    /// Cryptographic verification failed.
    Verification(VerificationError),
    /// The authenticated bytes are not valid tree JSON.
    Json(covalence_lib_json::Error),
    /// The authenticated tree is not a closed, well-typed term.
    Check(CheckError),
    /// The authenticated closed term does not have Boolean type.
    ExpectedBoolean,
}

impl fmt::Display for ImportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedVersion(version) => {
                write!(
                    formatter,
                    "unsupported closed theorem JSON version {version}"
                )
            }
            Self::PayloadHashMismatch => formatter.write_str("signed payload hash mismatch"),
            Self::UntrustedSigner(key) => write!(formatter, "untrusted theorem signer {key}"),
            Self::Verification(error) => {
                write!(formatter, "signature verification failed: {error}")
            }
            Self::Json(error) => write!(formatter, "signed payload is not HOL JSON: {error}"),
            Self::Check(error) => write!(formatter, "signed term failed checking: {error}"),
            Self::ExpectedBoolean => formatter.write_str("signed term is not Boolean"),
        }
    }
}

impl Error for ImportError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Verification(error) => Some(error),
            Self::Json(error) => Some(error),
            Self::Check(error) => Some(error),
            Self::UnsupportedVersion(_)
            | Self::PayloadHashMismatch
            | Self::UntrustedSigner(_)
            | Self::ExpectedBoolean => None,
        }
    }
}

/// A closed Boolean theorem accepted from an explicitly trusted signer.
///
/// This is an external trust leaf, not a local HOL derivation. It remains
/// distinct from [`Theorem`] in this proof of concept.
#[derive(Clone, Debug)]
pub struct ImportedTheorem {
    conclusion: Tree,
    signer: O256,
    payload_hash: O256,
}

impl ImportedTheorem {
    /// Imported closed Boolean conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> &Tree {
        &self.conclusion
    }

    /// Explicit external authority that signed the conclusion.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.signer
    }

    /// Hash of the exact authenticated JSON bytes.
    #[must_use]
    pub const fn payload_hash(&self) -> O256 {
        self.payload_hash
    }
}

/// In-memory local policy naming external theorem authorities.
#[derive(Default)]
pub struct TrustedSigners<'a> {
    verifiers: BTreeMap<O256, &'a dyn Verifier>,
}

impl<'a> TrustedSigners<'a> {
    /// Creates an empty policy. No artifact is trusted by default.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            verifiers: BTreeMap::new(),
        }
    }

    /// Explicitly trusts `verifier` as the authority named by `key`.
    pub fn trust(&mut self, key: O256, verifier: &'a dyn Verifier) {
        self.verifiers.insert(key, verifier);
    }

    /// Authenticates, parses, and checks one external closed theorem.
    ///
    /// Verification authenticates an external authority; it is not evidence of
    /// a local HOL derivation.
    ///
    /// # Errors
    ///
    /// Rejects unsupported versions, changed bytes, untrusted/invalid
    /// signatures, malformed JSON, open syntax, and non-Boolean terms.
    pub fn import(&self, artifact: &SignedClosedTheorem) -> Result<ImportedTheorem, ImportError> {
        if artifact.version != CLOSED_THEOREM_JSON_VERSION {
            return Err(ImportError::UnsupportedVersion(artifact.version));
        }
        let payload_hash = O256::from_bytes(&artifact.payload);
        if payload_hash.as_bytes() != &artifact.payload_hash {
            return Err(ImportError::PayloadHashMismatch);
        }
        let key = O256::from_array(artifact.signer);
        let verifier = self
            .verifiers
            .get(&key)
            .ok_or(ImportError::UntrustedSigner(key))?;
        verifier
            .verify(
                key,
                closed_theorem_json_statement(payload_hash),
                &artifact.signature,
            )
            .map_err(ImportError::Verification)?;
        let conclusion =
            covalence_lib_json::from_slice::<Tree>(&artifact.payload).map_err(ImportError::Json)?;
        let r#type = check_closed(&conclusion).map_err(ImportError::Check)?;
        if r#type != Tree::bool_ty() {
            return Err(ImportError::ExpectedBoolean);
        }
        Ok(ImportedTheorem {
            conclusion,
            signer: key,
            payload_hash,
        })
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_crypto::ed25519::SigningKey;

    use super::*;
    use crate::{Ed25519Signer, Ed25519Verifier, ed25519_key_id, valid_snapshot_statement};

    fn keys(byte: u8) -> (Ed25519Signer, Ed25519Verifier, O256) {
        let signing_key = SigningKey::from_bytes(&[byte; 32]);
        let key = ed25519_key_id(signing_key.verifying_key().as_bytes());
        (
            Ed25519Signer::new(signing_key.clone()),
            Ed25519Verifier::new(signing_key.verifying_key()),
            key,
        )
    }

    fn sign_payload(payload: Vec<u8>, signer: &dyn Signer, key: O256) -> SignedClosedTheorem {
        let payload_hash = O256::from_bytes(&payload);
        SignedClosedTheorem {
            version: CLOSED_THEOREM_JSON_VERSION,
            payload,
            payload_hash: payload_hash.into_bytes(),
            signer: key.into_bytes(),
            signature: signer
                .sign(key, closed_theorem_json_statement(payload_hash))
                .expect("sign test payload")
                .to_vec(),
        }
    }

    #[test]
    fn derived_truth_signs_serializes_and_imports() {
        let (signer, verifier, key) = keys(7);
        let artifact = sign_closed_theorem(&Theorem::truth(), &signer, key).expect("export");
        let wire = covalence_lib_json::to_vec(&artifact).expect("serialize envelope");
        let decoded: SignedClosedTheorem =
            covalence_lib_json::from_slice(&wire).expect("deserialize envelope");
        let mut policy = TrustedSigners::new();
        policy.trust(key, &verifier);
        let imported = policy.import(&decoded).expect("import");

        assert_eq!(imported.conclusion(), &Tree::bool(true));
        assert_eq!(imported.signer(), key);
        assert_eq!(imported.payload_hash().as_bytes(), &decoded.payload_hash);
    }

    #[test]
    fn changed_bytes_wrong_domains_and_untrusted_keys_fail() {
        let (signer, verifier, key) = keys(7);
        let mut artifact = sign_closed_theorem(&Theorem::truth(), &signer, key).expect("export");
        let empty_policy = TrustedSigners::new();
        assert!(matches!(
            empty_policy.import(&artifact),
            Err(ImportError::UntrustedSigner(_))
        ));

        let mut policy = TrustedSigners::new();
        policy.trust(key, &verifier);
        artifact.payload.push(b' ');
        assert!(matches!(
            policy.import(&artifact),
            Err(ImportError::PayloadHashMismatch)
        ));

        let payload = covalence_lib_json::to_vec(Theorem::truth().conclusion()).expect("json");
        let payload_hash = O256::from_bytes(&payload);
        let wrong_signature = signer
            .sign(key, valid_snapshot_statement(payload_hash))
            .expect("wrong-domain signature");
        let wrong_domain = SignedClosedTheorem {
            version: CLOSED_THEOREM_JSON_VERSION,
            payload,
            payload_hash: payload_hash.into_bytes(),
            signer: key.into_bytes(),
            signature: wrong_signature.to_vec(),
        };
        assert!(matches!(
            policy.import(&wrong_domain),
            Err(ImportError::Verification(_))
        ));
    }

    #[test]
    fn valid_signatures_do_not_bypass_syntax_scope_or_type_checks() {
        let (signer, verifier, key) = keys(9);
        let mut policy = TrustedSigners::new();
        policy.trust(key, &verifier);

        for (payload, expected) in [
            (b"not json".to_vec(), "json"),
            (
                covalence_lib_json::to_vec(&Tree::bound(0)).expect("open JSON"),
                "check",
            ),
            (
                covalence_lib_json::to_vec(&Tree::free(0)).expect("free JSON"),
                "check",
            ),
            (
                covalence_lib_json::to_vec(&Tree::zero()).expect("non-bool JSON"),
                "bool",
            ),
        ] {
            let error = policy
                .import(&sign_payload(payload, &signer, key))
                .expect_err("must reject");
            match (expected, error) {
                ("json", ImportError::Json(_))
                | ("check", ImportError::Check(_))
                | ("bool", ImportError::ExpectedBoolean) => {}
                (_, other) => panic!("unexpected error: {other}"),
            }
        }
    }
}
