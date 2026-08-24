//! Minimal proof component using the standard Nucleus proof ABI.

// `cargo component` generates the canonical-ABI glue. It intentionally uses
// low-level casts and naming patterns that are outside this crate's style.
#[allow(
    unsafe_code,
    warnings,
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::restriction
)]
#[cfg(target_os = "wasi")]
mod bindings;

#[cfg(target_os = "wasi")]
use bindings::{
    exports::nucleus::proof::standard::Guest,
    nucleus::proof::host::{Bytes, IndexCas, Kernel, SynRel, cas_get, cas_insert},
};

#[cfg(target_os = "wasi")]
struct Component;

#[cfg(target_os = "wasi")]
impl Guest for Component {
    fn prove() -> Result<Kernel, String> {
        let bytes = Bytes::new(b"nucleus proof demo");
        let blob = bytes.blob();
        if blob.bytes().to_list() != b"nucleus proof demo" {
            return Err("blob-to-bytes conversion changed the payload".to_owned());
        }

        let private = IndexCas::new();
        let private_id = private.insert(&blob);
        if private.get(private_id).is_none() {
            return Err("private CAS did not retain the blob".to_owned());
        }

        let default_id = cas_insert(&blob);
        if cas_get(default_id).is_none() {
            return Err("default CAS did not retain the blob".to_owned());
        }

        let kernel = Kernel::new();
        let star = kernel.kind_star()?;
        let bool_ty = kernel.bool_type(star)?;
        let truth = kernel.bool_lit(bool_ty, true)?;
        let reflexivity = kernel.syn_refl(SynRel::Syn, truth, None)?;
        if kernel.syn_fact_count() != 1 {
            return Err("unexpected syntactic-fact slot count".to_owned());
        }
        kernel.union_syn_fact(reflexivity)?;
        if !kernel.remove_syn_fact(reflexivity) {
            return Err("could not remove the syntactic fact".to_owned());
        }
        kernel.truncate_syn_facts(0)?;
        Ok(kernel)
    }
}

#[cfg(target_os = "wasi")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
