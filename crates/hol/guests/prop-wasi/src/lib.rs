//! Proof-module guest fixture that also speaks WASI preview 1.
//!
//! Compiled to `wasm32-wasip1`, this guest is an ordinary Rust library
//! using `std`: it prints progress through WASI stdout while proving
//! `|- true` through the `nucleus-logic` imports. Runners that have not
//! enabled WASI for this module refuse it at instantiation, which is a
//! clean reported failure. On native targets the crate is empty.

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)]
mod guest {
    use covalence_hol_guest_sdk as api;

    /// Proves `|- true` in the empty context, narrating over stdout.
    #[unsafe(no_mangle)]
    pub extern "C" fn prove() -> i64 {
        println!("wasi guest: proving |- true");
        let vars = api::vars_bool(0);
        if vars < 0 {
            return 1;
        }
        let theorem = api::truth(vars);
        if theorem < 0 {
            return 2;
        }
        if api::finish(theorem) < 0 {
            return 3;
        }
        println!("wasi guest: finished theorem {theorem}");
        0
    }
}
