//! Portable trusted core for Nucleus.

#![deny(unsafe_code)]

#[cfg(target_os = "wasi")]
#[allow(unsafe_code)]
#[rustfmt::skip]
mod bindings;

mod expr;
mod knowledge;
mod normalized;
mod trusted_db;

pub use expr::{Bool, EvalError, Expr, Prop, PropContext, Sort};
pub use knowledge::{
    Def, InstallKnowledgeOutcome, KnowledgeError, KnowledgeModel, ReplSession, SuccessfulOutput,
    SuccessfulTraceQuery, TermIdentity, TermTraceIdentity, TypeIdentity, Use,
};
pub use normalized::{
    ExecutionModel, ExecutionModelError, ExecutorId, ExpressionId, InstallExecutionModelOutcome,
    TraceId, TraceOutcome,
};
pub use trusted_db::{
    CatalogError, InstallOutcome, Metatable, NeutronCatalog, RustTypeId, RustTypes, TrustedDb,
    TrustedDbError,
};

/// Returns a stable value used by cross-target smoke tests.
///
/// # Panics
///
/// Panics if the linked `SQLite` runtime cannot execute the smoke query.
#[must_use]
#[cfg_attr(
    all(target_arch = "wasm32", target_os = "unknown"),
    wasm_bindgen::prelude::wasm_bindgen
)]
pub fn smoke() -> u32 {
    covalence_neutron::sqlite_smoke().expect("SQLite smoke query should succeed")
}

#[cfg(target_os = "wasi")]
struct Component;

#[cfg(target_os = "wasi")]
impl bindings::Guest for Component {
    fn smoke() -> u32 {
        smoke()
    }
}

#[cfg(target_os = "wasi")]
#[allow(unsafe_code)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}

#[cfg(test)]
mod tests {
    #[test]
    fn smoke_value_is_stable() {
        assert_eq!(super::smoke(), 42);
    }
}
