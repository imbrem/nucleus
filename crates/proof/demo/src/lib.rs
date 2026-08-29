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
#[cfg(target_arch = "wasm32")]
mod bindings;

#[cfg(target_arch = "wasm32")]
mod tactic;

#[cfg(target_arch = "wasm32")]
use bindings::{
    exports::nucleus::proof::standard::Guest,
    nucleus::proof::host::{
        Bytes, IndexCas, Kernel, Sort, SynRel, cas_get, cas_get_bytes, cas_insert,
    },
};

#[cfg(target_arch = "wasm32")]
struct Component;

#[cfg(target_arch = "wasm32")]
impl Component {
    async fn prove_requested(requested: &[u8], kernel: Kernel) -> Result<Kernel, String> {
        // The zero selector conventionally requests this component's default
        // proof. Its input is independently addressed in the default CAS.
        const INPUT: [u8; 32] = [
            0x02, 0xc4, 0xf6, 0x10, 0xbb, 0x41, 0xad, 0x65, 0x2b, 0xf8, 0x7d, 0x0d, 0xba, 0x85,
            0x83, 0xd8, 0x99, 0xd0, 0x94, 0x79, 0xef, 0x66, 0x32, 0x86, 0xf3, 0xb3, 0xa1, 0x61,
            0xc2, 0x2c, 0x09, 0xcf,
        ];
        let input_address = if requested.is_empty() || requested.iter().all(|byte| *byte == 0) {
            INPUT.as_slice()
        } else {
            requested
        };
        let fetched = cas_get_bytes(input_address.to_vec())
            .await?
            .ok_or_else(|| "proof input is absent from the default CAS".to_owned())?;
        if fetched.to_list() != b"nucleus proof demo" {
            return Err("async CAS fetch changed the proof input".to_owned());
        }

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

        let star = kernel.kind_star()?;
        let bool_ty = kernel.bool_type(star)?;
        let truth = kernel.bool_lit(bool_ty, true)?;

        // Run a userspace rewrite accelerator through its imported component
        // interface. REFL gives `|- true = true`; EQT_ELIM gives `|- true`;
        // the host tactic asks checked EQ_MP to transport that premise.
        let equality = kernel.refl(bool_ty, truth)?;
        let premise = kernel.eqt_elim(equality.theorem)?;
        let rewritten = tactic::rewrite(&kernel, bool_ty, equality.theorem, premise)?;
        if rewritten.source != truth || rewritten.target != truth {
            return Err("userspace rewrite changed a reflexive proposition".to_owned());
        }

        let reflexivity = kernel.syn_refl(SynRel::Syn, truth, None)?;
        if kernel.syn_fact_count() != 1 {
            return Err("unexpected syntactic-fact slot count".to_owned());
        }
        kernel.union_syn_fact(reflexivity)?;
        if !kernel.remove_syn_fact(reflexivity) {
            return Err("could not remove the syntactic fact".to_owned());
        }
        kernel.truncate_syn_facts(0)?;

        // Carve a guarded subtype out of `bool` along `\x. x`, through the
        // subtype axiom, and rebuild the package around it. The kernel supplies
        // only the sentence; the subtype, `rep` and `abs` are ordinary
        // construction on top, which is the point of the split.
        kernel.add_axiom("ax.sub")?;
        let variable = kernel.tm_fv(0, bool_ty)?;
        let predicate = kernel.lam(variable, variable)?;
        let axiom = kernel.sub_exists(bool_ty, bool_ty, predicate)?;
        if axiom.base_name != 1 {
            return Err("the package should start one past the caller's names".to_owned());
        }
        if kernel.fresh_name(&[bool_ty, predicate])? != axiom.base_name {
            return Err("fresh-name disagreed with the axiom's own choice".to_owned());
        }

        let sub = kernel.model(axiom.model_name, axiom.package_body)?;
        let rep_ty = kernel.ty_arr(sub, axiom.carrier)?;
        let representation = kernel.tm_fv(axiom.base_name + 1, rep_ty)?;
        // A law about the chosen representation, built from the derived logic.
        let value = kernel.tm_fv(axiom.base_name + 4, sub)?;
        let applied = kernel.app(representation, value)?;
        let reflexive = kernel.tm_eq(bool_ty, applied, applied)?;
        let quantified = kernel.forall_tm(bool_ty, value, reflexive)?;
        if kernel.category(quantified)? != Sort::Tm {
            return Err("a quantified law should be a term".to_owned());
        }

        Ok(kernel)
    }
}

#[cfg(target_arch = "wasm32")]
impl Guest for Component {
    async fn prove_addr(addr: Vec<u8>, kernel: Kernel) -> Result<Kernel, String> {
        if addr.len() != 32 {
            return Err(format!(
                "O256 proof selectors contain 32 bytes, got {}",
                addr.len()
            ));
        }
        Self::prove_requested(&addr, kernel).await
    }

    async fn prove_name(name: String, kernel: Kernel) -> Result<Kernel, String> {
        if name != "default" {
            return Err(format!("unknown textual proof name {name:?}"));
        }
        Self::prove_requested(&[], kernel).await
    }

    async fn prove_ix(ix: u64, kernel: Kernel) -> Result<Kernel, String> {
        if ix != 0 {
            return Err(format!("unknown proof mutation index {ix}"));
        }
        Self::prove_requested(&[], kernel).await
    }

    async fn prove_bytes(bytes: Bytes, kernel: Kernel) -> Result<Kernel, String> {
        if bytes.to_list() != b"default" {
            return Err(format!("unknown byte proof name of length {}", bytes.len()));
        }
        Self::prove_requested(&[], kernel).await
    }
}

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
