//! Portable Nucleus facade with an explicit trusted-core assembly.

/// Auditable assembly of the checked Nucleus authority surface.
pub use covalence_nucleus_core as core;

/// Untrusted S-expression parsing, elaboration, metadata, and init tooling.
pub use covalence_nucleus_script as script;

/// Untrusted high-level proof programs over checked kernel operations.
pub use covalence_nucleus_tactics as tactics;

/// Compatibility name for the formerly HOL-specific frontend module.
pub use covalence_nucleus_script as hol_script;

// Preserve the existing facade while making `core` the single assembly site.
pub use core::{
    ChosenModel, ExistsError, Infinity, InfinityError, InfinityExt, ModelError, ModelExt,
    NaturalError, NaturalExt, Naturals, OpenedExists, Substitution, Subtype, SubtypeError,
    SubtypeExt, cas, hol, open_exists, substitute,
};

/// The first in-memory CAS utility exposed by the Nucleus facade.
pub use covalence_data_cas::IndexCas;

#[cfg(not(target_arch = "wasm32"))]
mod proof;

#[cfg(not(target_arch = "wasm32"))]
mod script_proof;

#[cfg(not(target_arch = "wasm32"))]
pub use proof::{
    ProofError, ProofInstance, ProofName, load_proof, load_proof_async, load_proof_with_cas_async,
};

#[cfg(not(target_arch = "wasm32"))]
pub use script_proof::{ScriptProofError, ScriptProofOutput, run_script_proofs};

mod snapshot;

pub use snapshot::{
    COV_VALID_DB_V0, ED25519_PUBLIC_KEY_V0, Ed25519Signer, Ed25519Verifier, SignError, Signer,
    VerificationError, Verifier, ed25519_key_id, valid_snapshot_statement,
};

#[cfg(target_os = "wasi")]
#[allow(unsafe_code)]
#[rustfmt::skip]
mod bindings;

/// Returns a stable value used by cross-target component smoke tests.
#[must_use]
#[cfg_attr(
    all(target_arch = "wasm32", target_os = "unknown"),
    wasm_bindgen::prelude::wasm_bindgen
)]
pub fn smoke() -> u32 {
    42
}

#[cfg(target_os = "wasi")]
struct Component;

#[cfg(target_os = "wasi")]
impl bindings::Guest for Component {
    fn smoke() -> u32 {
        smoke()
    }
}

#[cfg(target_os = "wasi")]
#[allow(unsafe_code)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}

#[cfg(test)]
mod tests {
    #[test]
    fn smoke_value_is_stable() {
        assert_eq!(super::smoke(), 42);
    }
}
