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
use bindings::{
    exports::nucleus::proof::strategy::Guest as StrategyGuest, nucleus::proof::host::Kernel,
};

#[cfg(target_arch = "wasm32")]
struct Component;

#[cfg(target_arch = "wasm32")]
impl StrategyGuest for Component {
    async fn apply_tactic(
        _tactic_id: u64,
        _arguments: Vec<u8>,
        kernel: Option<Kernel>,
    ) -> Result<Kernel, String> {
        Self::reject(kernel.unwrap_or_else(Kernel::new))
    }
}

#[cfg(target_arch = "wasm32")]
impl Component {
    fn reject(kernel: Kernel) -> Result<Kernel, String> {
        let star = kernel.kind_star()?;
        let message = match kernel.bool_lit(star, true) {
            Ok(_) => "kernel accepted a kind where a boolean type was required".to_owned(),
            Err(error) => format!("demo invalid proof was rejected: {error}"),
        };
        drop(kernel);
        Err(message)
    }
}

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
