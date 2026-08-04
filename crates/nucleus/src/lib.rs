//! Portable trusted core for Nucleus.

mod connection;
pub mod hol;
mod kernel;

pub use connection::Connection;
pub use hol::{
    AllowAll, AuthenticatedHolImageValidationError, AuthenticatedValidatedHolImage, ContextError,
    ContextId, ContextImplication, ExportError, ExportId, ExportSort, ExportView,
    ExternalExportRef, Hol, HolDatabaseRef, HolExportError, HolImageCounts,
    HolImageValidationError, HolOpenError, HolSchema, HolSchemaDescriptor,
    HolSchemaDescriptorError, HolSnapshotAttestation, ImportError, ImportId, ImportView,
    ImportedContextId, ImportedExport, ImportedHolReader, ImportedKindId, ImportedReaderError,
    ImportedTermId, ImportedTermView, ImportedTypeId, Kind, KindError, KindId, KindView,
    MatchedTrustedHolImage, MetadataError, MetadataSchemaError, MetadataTable, MetadataTarget,
    MetadataType, MetadataValue, NamespaceError, NamespaceExport, NamespaceId, NamespaceSource,
    NamespaceView, Operation, Policy, ProofError, ProofSession, SignedHolSnapshot,
    SnapshotTrustError, TermError, TermId, TermView, Theorem, TrustedImportError, TrustedImportId,
    TrustedImportImageError, TrustedImportView, TypeError, TypeId, TypeView, UnboundVariable,
    ValidatedHolImage, stlc_bool_eq_v0_schema_id, stlc_bool_eq_v0_semantics,
};
pub use kernel::Kernel;

#[path = "repl.rs"]
pub mod sql;
pub use sql::Sql;

mod snapshot;

pub use snapshot::{
    AuthenticatedSnapshot, AuthenticatedSnapshotClaim, COV_SCHEMA_VALID_DB_V0, COV_VALID_DB_V0,
    ED25519_PUBLIC_KEY_V0, Ed25519Signer, Ed25519Verifier, SignError, SignedSnapshotAttestation,
    SignedSnapshotEnvelope, Signer, SnapshotAuthenticationError, VerificationError, Verifier,
    ed25519_key_id, schema_valid_snapshot_statement, valid_snapshot_statement,
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
