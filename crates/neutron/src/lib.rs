//! Mechanical access to relational-state instances.
//!
//! This crate can inspect arbitrary `SQLite` connections. Its outputs are
//! structural candidates, not trusted catalogs, groundings, or theorems.

#![deny(unsafe_code)]

mod names;
mod scan;

pub use names::{
    BOOL_SORT_V0, BOOL_VALUES_RELATION_V0, BOOTSTRAP_CATALOG, INTEGER_BOOL_01_REPR_V0,
    MetatableKind, metatable_name, parse_metatable_name,
};
pub use scan::{
    CatalogCandidate, FieldDeclaration, KnownMetatable, ScanError, UnknownMetatable,
    scan_metatables,
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
