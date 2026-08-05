//! Semantic adapter from capability-free core-Wasm output to an untrusted HOL recipe.

use std::error::Error as StdError;
use std::fmt;

use covalence_proton::{
    CoreWasmOwnedBytesError, CoreWasmOwnedBytesLimits, CoreWasmOwnedBytesRuntime,
};

use crate::{HolProofRecipeError, SealedHolProofRecipe};

/// Runs a no-import core-Wasm producer and decodes its copied bytes as a canonical recipe.
///
/// The executor receives only module bytes and returns only bytes. It never receives a kernel,
/// connection, database, or signing key. This adapter still proves nothing: checked replay is a
/// separate caller-controlled operation.
///
/// # Errors
///
/// Returns an error if the module violates the mechanical ABI or if its bytes are not one exact,
/// bounded canonical HOL recipe.
pub fn execute_core_wasm_hol_recipe(
    module: &[u8],
) -> Result<SealedHolProofRecipe, CoreWasmHolRecipeError> {
    let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default())
        .map_err(CoreWasmHolRecipeError::Runtime)?;
    let bytes = runtime
        .execute(module)
        .map_err(CoreWasmHolRecipeError::Runtime)?;
    SealedHolProofRecipe::from_untrusted_bytes(&bytes).map_err(CoreWasmHolRecipeError::Recipe)
}

/// Failure in the mechanical executor or authoritative recipe decoder.
#[derive(Debug)]
pub enum CoreWasmHolRecipeError {
    /// The core-Wasm module violated the capability-free owned-bytes contract.
    Runtime(CoreWasmOwnedBytesError),
    /// The returned bytes were not a canonical, structurally valid recipe.
    Recipe(HolProofRecipeError),
}

impl fmt::Display for CoreWasmHolRecipeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Runtime(error) => write!(formatter, "core-Wasm recipe guest failed: {error}"),
            Self::Recipe(error) => write!(formatter, "core-Wasm guest returned {error}"),
        }
    }
}

impl StdError for CoreWasmHolRecipeError {}

#[cfg(test)]
mod tests {
    use covalence_nucleus::Kernel;

    use super::*;
    use crate::hol_guest_plan::closed_beta_test_recipe;

    fn unsigned_leb(mut value: u64, bytes: &mut Vec<u8>) {
        loop {
            let byte = u8::try_from(value & 0x7f).expect("seven bits fit u8");
            value >>= 7;
            bytes.push(if value == 0 { byte } else { byte | 0x80 });
            if value == 0 {
                return;
            }
        }
    }

    fn signed_leb(mut value: i64, bytes: &mut Vec<u8>) {
        loop {
            let byte = u8::try_from(value & 0x7f).expect("seven bits fit u8");
            value >>= 7;
            let done = (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0);
            bytes.push(if done { byte } else { byte | 0x80 });
            if done {
                return;
            }
        }
    }

    fn name(value: &str, bytes: &mut Vec<u8>) {
        unsigned_leb(
            u64::try_from(value.len()).expect("Wasm name length fits u64"),
            bytes,
        );
        bytes.extend_from_slice(value.as_bytes());
    }

    fn section(id: u8, payload: &[u8], module: &mut Vec<u8>) {
        module.push(id);
        unsigned_leb(
            u64::try_from(payload.len()).expect("Wasm section length fits u64"),
            module,
        );
        module.extend_from_slice(payload);
    }

    fn closed_beta_module() -> Vec<u8> {
        // This wire fixture is independently asserted against the SDK encoder in that crate.
        // Keeping the verifier-side fixture dependency-free also keeps the SDK out of the
        // authoritative decoder/replay dependency graph.
        const RECIPE: &[u8] = &[
            6, 0, 11, 0, 8, // header
            0, // bool type
            1, 0, 0, 0, 0, 0, 0, // bound 0 : bool
            2, 0, 0, 0, 1, // lambda
            3, 1, // true
            4, // empty context
            0x35, 0, 2, 0, 3, // beta
            0x38, 0, 4, 0, 5, // conversion equality
            6, 0, 6, // persist
            7, 1, 0, 4, b'd', b'e', b'm', b'o', // namespace
            9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, // context export
            8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, // theorem export
        ];
        let recipe = RECIPE;
        let pointer = 32_u32;
        let length = u32::try_from(recipe.len()).expect("closed-beta recipe fits the ABI");
        let descriptor = (u64::from(length) << 32) | u64::from(pointer);
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        section(1, &[1, 0x60, 0, 1, 0x7e], &mut module);
        section(3, &[1, 0], &mut module);
        section(5, &[1, 1, 1, 1], &mut module);
        let mut exports = vec![2];
        name("memory", &mut exports);
        exports.extend_from_slice(&[2, 0]);
        name("covalence_owned_bytes", &mut exports);
        exports.extend_from_slice(&[0, 0]);
        section(7, &exports, &mut module);
        let mut function = vec![0, 0x42];
        signed_leb(descriptor.cast_signed(), &mut function);
        function.push(0x0b);
        let mut code = vec![1];
        unsigned_leb(
            u64::try_from(function.len()).expect("test function length fits u64"),
            &mut code,
        );
        code.extend_from_slice(&function);
        section(10, &code, &mut module);
        let mut data = vec![
            1,
            0,
            0x41,
            u8::try_from(pointer).expect("small pointer"),
            0x0b,
        ];
        unsigned_leb(
            u64::try_from(recipe.len()).expect("recipe length fits u64"),
            &mut data,
        );
        data.extend_from_slice(recipe);
        section(11, &data, &mut module);
        module
    }

    #[test]
    fn canonical_beta_wire_exactly_decodes_and_replays() {
        let recipe = execute_core_wasm_hol_recipe(&closed_beta_module()).unwrap();
        assert_eq!(recipe, closed_beta_test_recipe());
        let kernel = Kernel::ephemeral();
        let signed = recipe.replay(&kernel).unwrap();
        assert_eq!(signed.signer(), kernel.key_id());
    }

    #[test]
    fn configured_real_core_wasm_beta_guest_exactly_decodes_and_replays() {
        let Some(module) = std::env::var_os("COVALENCE_CORE_WASM_BETA_GUEST") else {
            return;
        };
        let bytes = std::fs::read(module).expect("read configured core-Wasm beta guest");
        let recipe = execute_core_wasm_hol_recipe(&bytes).expect("execute configured guest");
        assert_eq!(recipe, closed_beta_test_recipe());
        let kernel = Kernel::ephemeral();
        let signed = recipe
            .replay(&kernel)
            .expect("replay configured guest recipe");
        assert_eq!(signed.signer(), kernel.key_id());
    }
}
