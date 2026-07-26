//! Mechanical access to relational-state instances.
//!
//! This crate can inspect arbitrary `SQLite` connections. Its outputs are
//! structural candidates, not trusted catalogs, groundings, or theorems.

#![deny(unsafe_code)]

mod names;
mod scan;

pub use names::{
    BOOL_SORT_V0, BOOTSTRAP_CATALOG, EXECUTION_TRACES_INTERPRETATION_V0,
    EXECUTION_TRACES_METATABLE_V0, EXECUTORS_INTERPRETATION_V0, EXECUTORS_METATABLE_V0,
    EXPRESSIONS_INTERPRETATION_V0, EXPRESSIONS_METATABLE_V0, MetatableKind,
    RUST_TYPES_INTERPRETATION_V0, RUST_TYPES_METATABLE_V0, TABLE_INTERPRETATIONS_INTERPRETATION_V0,
    TABLE_INTERPRETATIONS_METATABLE_V0, metatable_name, parse_metatable_name,
};
pub use scan::{
    BootstrapCatalog, CatalogCandidate, MetatableDeclaration, ScanError, scan_metatables,
};

/// Exercises the linked `SQLite` runtime without making a trust claim.
///
/// # Errors
///
/// Returns the `SQLite` error if the runtime cannot execute the query.
pub fn sqlite_smoke() -> covalence_lib_sqlite::Result<u32> {
    let connection = covalence_lib_sqlite::Connection::open_in_memory()?;
    connection.execute("CREATE TABLE smoke (value INTEGER NOT NULL)", ())?;
    connection.execute("INSERT INTO smoke VALUES (42)", ())?;
    connection.query_row("SELECT value FROM smoke", (), |row| row.get(0))
}

#[cfg(test)]
mod tests {
    #[test]
    fn sqlite_runtime_is_available() {
        assert_eq!(super::sqlite_smoke(), Ok(42));
    }
}
