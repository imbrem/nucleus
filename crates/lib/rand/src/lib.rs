//! Randomness primitives used by Nucleus.

pub use rand;
pub use rand::*;

#[cfg(all(test, target_arch = "wasm32", target_os = "unknown"))]
mod tests {
    use super::random;
    use wasm_bindgen_test::wasm_bindgen_test;

    #[wasm_bindgen_test]
    fn javascript_host_supplies_randomness() {
        let first = random::<[u8; 32]>();
        let second = random::<[u8; 32]>();

        assert_ne!(first, second);
    }
}
