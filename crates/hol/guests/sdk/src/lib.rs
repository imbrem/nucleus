//! Guest-side bindings for the `nucleus-logic` import namespace.
//!
//! Proof modules link against these flat FFI imports to drive the HOL
//! kernel from inside a Wasm sandbox: resolve init-database exports,
//! build terms, invoke the out-of-TCB derived rules on integer handles,
//! read back conclusions, and record finished theorems. Every function
//! returns [`FAILURE`] when the host refuses an operation; handles are
//! opaque and only ever minted by the host.
//!
//! The bindings compile to real imports only on `wasm32` targets; on
//! native targets this crate is empty, so guest crates stay ordinary
//! workspace members.

#![cfg_attr(target_arch = "wasm32", no_std)]

/// The value host functions return when an operation fails.
pub const FAILURE: i64 = -1;

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)]
mod ffi {
    #[link(wasm_import_module = "nucleus-logic")]
    unsafe extern "C" {
        pub safe fn resolve(pointer: *const u8, length: usize) -> i64;
        pub safe fn vars_bool(count: i64) -> i64;
        pub safe fn tm_var(index: i64) -> i64;
        pub safe fn tm_app(function: i64, argument: i64) -> i64;
        pub safe fn truth(vars: i64) -> i64;
        pub safe fn assume(vars: i64, prop: i64) -> i64;
        pub safe fn conj(left: i64, right: i64) -> i64;
        pub safe fn conjunct1(theorem: i64) -> i64;
        pub safe fn conjunct2(theorem: i64) -> i64;
        pub safe fn disj1(theorem: i64, right: i64) -> i64;
        pub safe fn disj2(left: i64, theorem: i64) -> i64;
        pub safe fn mp(implication: i64, premise: i64) -> i64;
        pub safe fn disch(prop: i64, theorem: i64) -> i64;
        pub safe fn thm_concl(theorem: i64) -> i64;
        pub safe fn finish(theorem: i64) -> i64;
    }
}

/// Resolves an init-database export by name to a term handle.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn resolve(name: &str) -> i64 {
    ffi::resolve(name.as_ptr(), name.len())
}

/// Builds the variable context of `count` Boolean variables.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn vars_bool(count: i64) -> i64 {
    ffi::vars_bool(count)
}

/// Builds the de Bruijn term variable `index`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn tm_var(index: i64) -> i64 {
    ffi::tm_var(index)
}

/// Builds the application `function argument`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn tm_app(function: i64, argument: i64) -> i64 {
    ffi::tm_app(function, argument)
}

/// Applies a binary connective to two operands.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn apply2(connective: i64, left: i64, right: i64) -> i64 {
    let partial = ffi::tm_app(connective, left);
    if partial < 0 {
        return FAILURE;
    }
    ffi::tm_app(partial, right)
}

/// `TRUTH`: `|- true` in the given variable context.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn truth(vars: i64) -> i64 {
    ffi::truth(vars)
}

/// `ASSUME`: `{p} |- p` in the given variable context.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn assume(vars: i64, prop: i64) -> i64 {
    ffi::assume(vars, prop)
}

/// `CONJ`: from `|- p` and `|- q`, `|- and p q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn conj(left: i64, right: i64) -> i64 {
    ffi::conj(left, right)
}

/// `CONJUNCT1`: from `|- and p q`, `|- p`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn conjunct1(theorem: i64) -> i64 {
    ffi::conjunct1(theorem)
}

/// `CONJUNCT2`: from `|- and p q`, `|- q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn conjunct2(theorem: i64) -> i64 {
    ffi::conjunct2(theorem)
}

/// `DISJ1`: from `|- p`, `|- or p q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn disj1(theorem: i64, right: i64) -> i64 {
    ffi::disj1(theorem, right)
}

/// `DISJ2`: from `|- q`, `|- or p q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn disj2(left: i64, theorem: i64) -> i64 {
    ffi::disj2(left, theorem)
}

/// `MP`: from `|- imp p q` and `|- p`, `|- q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn mp(implication: i64, premise: i64) -> i64 {
    ffi::mp(implication, premise)
}

/// `DISCH`: from `A |- q`, `A \ {p} |- imp p q`.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn disch(prop: i64, theorem: i64) -> i64 {
    ffi::disch(prop, theorem)
}

/// Reads the conclusion term of a theorem handle (a trust-free query).
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn thm_concl(theorem: i64) -> i64 {
    ffi::thm_concl(theorem)
}

/// Records a finished theorem with the host.
#[cfg(target_arch = "wasm32")]
#[must_use]
pub fn finish(theorem: i64) -> i64 {
    ffi::finish(theorem)
}
