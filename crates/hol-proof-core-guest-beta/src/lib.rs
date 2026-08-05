#![cfg_attr(target_arch = "wasm32", no_std)]
//! Capability-free core-Wasm guest which returns one canonical proof recipe.

#[cfg(any(target_arch = "wasm32", test))]
use covalence_hol_proof_recipe_sdk::CLOSED_BETA_RECIPE;

/// Returns `(length << 32) | pointer` for bytes owned by this module's exported memory.
///
/// The packed descriptor is one observation point: the host does not call separate guest
/// functions which could mutate memory between returning the pointer and length.
#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)] // `no_mangle` names the two-scalar core-Wasm ABI; no unsafe block is used.
#[unsafe(no_mangle)]
pub extern "C" fn covalence_owned_bytes() -> i64 {
    let pointer = CLOSED_BETA_RECIPE.as_ptr() as usize as u32;
    let length = CLOSED_BETA_RECIPE.len() as u32;
    ((u64::from(length) << 32) | u64::from(pointer)) as i64
}

#[cfg(all(target_arch = "wasm32", not(test)))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recipe_is_guest_owned_static_data() {
        assert!(!CLOSED_BETA_RECIPE.is_empty());
    }
}
