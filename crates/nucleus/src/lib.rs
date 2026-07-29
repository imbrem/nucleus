//! Portable trusted core for Nucleus.

mod cas;
mod catalog;
mod connection;
mod invariant;

pub use cas::{Cas, CasError, CasId};
pub use catalog::{CONNECTION_CATALOG, Catalog, CatalogEntry, CatalogError, DB_CATALOG};
pub use connection::{
    ATTACHED_DATABASES, ATTACHED_DATABASES_INTERPRETATION, Connection, ConnectionError,
    DEFAULT_CAS, DEFAULT_CAS_INTERPRETATION,
};
pub use invariant::{Invariant, Standard, Unchecked};

mod snapshot;

pub use snapshot::{
    COV_VALID_DB_V0, ED25519_PUBLIC_KEY_V0, Ed25519Signer, Ed25519Verifier, SignError, Signer,
    VerificationError, Verifier, ed25519_key_id, valid_snapshot_statement,
};

#[cfg(target_os = "wasi")]
#[allow(unsafe_code)]
#[rustfmt::skip]
mod bindings;

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
    sqlite_smoke().expect("SQLite smoke query should succeed")
}

fn sqlite_smoke() -> covalence_lib_sqlite::Result<u32> {
    let connection = covalence_lib_sqlite::Connection::open_in_memory()?;
    connection.execute("CREATE TABLE smoke (value INTEGER NOT NULL)", ())?;
    connection.execute("INSERT INTO smoke VALUES (42)", ())?;
    connection.query_row("SELECT value FROM smoke", (), |row| row.get(0))
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
