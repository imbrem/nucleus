//! Portable trusted core for Nucleus.

mod connection;

pub use connection::{Connection, ConnectionError};

mod snapshot;

pub use snapshot::{
    AuthenticatedSnapshot, AuthenticatedSnapshotClaim, COV_SCHEMA_VALID_DB_V0,
    ED25519_PUBLIC_KEY_V0, Ed25519Signer, Ed25519Verifier, SignError, SignedSnapshotAttestation,
    SignedSnapshotEnvelope, Signer, SnapshotAuthenticationError, VerificationError, Verifier,
    ed25519_key_id, schema_valid_snapshot_statement,
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
    use covalence_lib_sqlite::{Statement, Step};

    let connection = covalence_lib_sqlite::Connection::open_in_memory()?;
    Statement::execute_batch(
        &connection,
        "CREATE TABLE smoke (value INTEGER NOT NULL); INSERT INTO smoke VALUES (42);",
    )?;
    let mut statement = Statement::prepare(&connection, "SELECT value FROM smoke")?;
    if statement.step()? == Step::Row
        && let Some(value) = statement.column(0).as_integer()
    {
        return Ok(u32::try_from(value).unwrap_or(0));
    }
    Ok(0)
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
