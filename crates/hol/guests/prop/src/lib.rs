//! Proof-module guest fixture: conjunction commutativity.
//!
//! Compiled to `wasm32-unknown-unknown`, this guest proves
//! `and p q |- and q p` for two Boolean variables entirely through the
//! `nucleus-logic` imports, checks mid-proof what its theorem handle
//! actually concluded, and records the result with the host. On native
//! targets the crate is empty.

#![cfg_attr(target_arch = "wasm32", no_std)]

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)]
mod guest {
    use covalence_hol_guest_sdk as api;

    /// Proves `and p q |- and q p` and finishes with the theorem.
    ///
    /// Returns 0 on success and a distinct positive step number on the
    /// first failed host call, so runner tests can tell where a broken
    /// run stopped.
    #[unsafe(no_mangle)]
    pub extern "C" fn prove() -> i64 {
        let and = api::resolve("and");
        if and < 0 {
            return 1;
        }
        let vars = api::vars_bool(2);
        if vars < 0 {
            return 2;
        }
        let p = api::tm_var(0);
        let q = api::tm_var(1);
        let p_and_q = api::apply2(and, p, q);
        if p_and_q < 0 {
            return 3;
        }
        let assumed = api::assume(vars, p_and_q);
        if assumed < 0 {
            return 4;
        }
        let left = api::conjunct1(assumed);
        let right = api::conjunct2(assumed);
        let swapped = api::conj(right, left);
        if swapped < 0 {
            return 5;
        }
        // A mid-proof read: confirm the handle concluded `and q p`
        // before recording it.
        let expected = api::apply2(and, q, p);
        if api::thm_concl(swapped) != expected {
            return 6;
        }
        if api::finish(swapped) < 0 {
            return 7;
        }
        0
    }

    #[panic_handler]
    fn panic(_: &core::panic::PanicInfo) -> ! {
        core::arch::wasm32::unreachable()
    }
}
