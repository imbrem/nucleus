//! Proof component demonstrating rejection through the standard Nucleus ABI.

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
use bindings::{exports::nucleus::proof::standard::Guest, nucleus::proof::host::Kernel};

#[cfg(target_arch = "wasm32")]
struct Component;

#[cfg(target_arch = "wasm32")]
impl Guest for Component {
    async fn prove(target: Vec<u8>) -> Result<Kernel, String> {
        if target.len() != 32 {
            return Err(format!(
                "proof targets contain 32 bytes, got {}",
                target.len()
            ));
        }
        let kernel = Kernel::new();
        let star = kernel.kind_star()?;
        match kernel.bool_lit(star, true) {
            Ok(_) => Err("kernel accepted a kind where a boolean type was required".to_owned()),
            Err(error) => Err(format!("demo invalid proof was rejected: {error}")),
        }
    }
}

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
