use std::collections::BTreeSet;

use covalence_lib_error::snafu;
use covalence_lib_sqlite::{Connection, OptionalExtension};
use snafu::Snafu;

use crate::names::{
    BOOTSTRAP_CATALOG, META_PREFIX, MetatableKind, metatable_name, parse_metatable_name,
};

/// A structurally decoded, non-authoritative description of metatables.
///
/// An arbitrary `SQLite` database may have no bootstrap catalog. The trusted
/// layer is responsible for requiring exactly one before accepting a database
/// as Nucleus state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogCandidate {
    bootstrap: Option<BootstrapCatalog>,
}

impl CatalogCandidate {
    /// Returns the bootstrap catalog when the database contains one.
    #[must_use]
    pub const fn bootstrap(&self) -> Option<&BootstrapCatalog> {
        self.bootstrap.as_ref()
    }
}

/// The permanent bootstrap catalog decoded from its fixed physical ABI.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BootstrapCatalog {
    declarations: Vec<MetatableDeclaration>,
}

impl BootstrapCatalog {
    /// Returns every extension metatable registered by the bootstrap.
    #[must_use]
    pub fn declarations(&self) -> &[MetatableDeclaration] {
        &self.declarations
    }
}

/// One extension metatable registered in the bootstrap catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MetatableDeclaration {
    table_name: String,
    interpretation: String,
}

impl MetatableDeclaration {
    /// Returns the physical extension-metatable name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table_name
    }

    /// Returns the interpretation selected for that table.
    #[must_use]
    pub fn interpretation(&self) -> &str {
        &self.interpretation
    }
}

/// Failure while structurally scanning metatables.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum ScanError {
    /// `SQLite` could not execute a structural query.
    #[snafu(display("could not inspect SQLite metadata: {source}"))]
    Sqlite {
        /// Underlying `SQLite` failure.
        source: covalence_lib_sqlite::Error,
    },
    /// A table used the reserved prefix without a canonical kind suffix.
    #[snafu(display("malformed reserved metatable name `{name}`"))]
    MalformedReservedName {
        /// Physical name.
        name: String,
    },
    /// The permanent bootstrap table had the wrong physical shape.
    #[snafu(display("invalid bootstrap catalog schema: {reason}"))]
    InvalidBootstrapSchema {
        /// Stable rejection detail.
        reason: String,
    },
    /// An extension registration was malformed.
    #[snafu(display("invalid metatable declaration: {reason}"))]
    InvalidDeclaration {
        /// Stable rejection detail.
        reason: String,
    },
    /// A reserved extension metatable was not registered by the bootstrap.
    #[snafu(display("unregistered metatable `{name}`"))]
    UnregisteredMetatable {
        /// Physical table name.
        name: String,
    },
    /// A declaration referenced a missing physical table.
    #[snafu(display("missing registered metatable `{name}`"))]
    MissingMetatable {
        /// Physical table name.
        name: String,
    },
}

impl ScanError {
    fn sqlite(source: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite { source }
    }
}

/// Scans metatables in `main` over an arbitrary borrowed `SQLite` connection.
///
/// Zero bootstrap catalogs is valid only when there are no other reserved
/// metatables. Every extension metatable must be indexed by the bootstrap.
/// This function performs no writes and makes no claim about trust, grounding,
/// completeness, or theorem authority.
///
/// # Errors
///
/// Rejects malformed reserved names, malformed bootstrap structure, missing or
/// unregistered extension metatables, and `SQLite` access failures.
pub fn scan_metatables(connection: &Connection) -> Result<CatalogCandidate, ScanError> {
    let names = physical_table_names(connection)?;
    let reserved = names
        .iter()
        .filter(|name| name.starts_with(META_PREFIX))
        .map(|name| {
            parse_metatable_name(name)
                .map(|kind| (name.clone(), kind))
                .ok_or_else(|| ScanError::MalformedReservedName { name: name.clone() })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let bootstrap_name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
    if !names.contains(&bootstrap_name) {
        if let Some((name, _)) = reserved.first() {
            return Err(ScanError::UnregisteredMetatable { name: name.clone() });
        }
        return Ok(CatalogCandidate { bootstrap: None });
    }

    validate_bootstrap_schema(connection)?;
    let declarations = read_declarations(connection)?;
    validate_extension_closure(connection, &reserved, &declarations)?;
    Ok(CatalogCandidate {
        bootstrap: Some(BootstrapCatalog { declarations }),
    })
}

fn physical_table_names(connection: &Connection) -> Result<BTreeSet<String>, ScanError> {
    let mut statement = connection
        .prepare("SELECT name FROM sqlite_schema WHERE type = 'table' ORDER BY name")
        .map_err(ScanError::sqlite)?;
    statement
        .query_map((), |row| row.get::<_, String>(0))
        .map_err(ScanError::sqlite)?
        .collect::<Result<BTreeSet<_>, _>>()
        .map_err(ScanError::sqlite)
}

fn validate_bootstrap_schema(connection: &Connection) -> Result<(), ScanError> {
    let name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
    if !table_is_strict(connection, &name)? {
        return Err(ScanError::InvalidBootstrapSchema {
            reason: String::from("bootstrap must be a STRICT table in main"),
        });
    }
    let columns = table_columns(connection, &name)?;
    let expected = [
        ("table_name", "TEXT", true, 1_u32),
        ("interpretation", "TEXT", true, 0),
    ];
    if columns.len() != expected.len()
        || !columns.iter().zip(expected).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(ScanError::InvalidBootstrapSchema {
            reason: String::from("columns do not match the permanent bootstrap ABI"),
        });
    }
    Ok(())
}

fn read_declarations(connection: &Connection) -> Result<Vec<MetatableDeclaration>, ScanError> {
    let name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
    let mut statement = connection
        .prepare(&format!(
            "SELECT table_name, interpretation FROM {} ORDER BY table_name",
            quote_identifier(&name)
        ))
        .map_err(ScanError::sqlite)?;
    statement
        .query_map((), |row| {
            Ok(MetatableDeclaration {
                table_name: row.get(0)?,
                interpretation: row.get(1)?,
            })
        })
        .map_err(ScanError::sqlite)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(ScanError::sqlite)
}

fn validate_extension_closure(
    connection: &Connection,
    reserved: &[(String, MetatableKind)],
    declarations: &[MetatableDeclaration],
) -> Result<(), ScanError> {
    let bootstrap_name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
    let registered = declarations
        .iter()
        .map(|declaration| declaration.table_name.as_str())
        .collect::<BTreeSet<_>>();

    for declaration in declarations {
        if declaration.table_name == bootstrap_name {
            return Err(ScanError::InvalidDeclaration {
                reason: String::from("the bootstrap is implicit and must not register itself"),
            });
        }
        if parse_metatable_name(&declaration.table_name).is_none() {
            return Err(ScanError::InvalidDeclaration {
                reason: format!(
                    "registered table `{}` is outside the canonical metatable namespace",
                    declaration.table_name
                ),
            });
        }
        if declaration.interpretation.is_empty() {
            return Err(ScanError::InvalidDeclaration {
                reason: format!(
                    "registered table `{}` has an empty interpretation",
                    declaration.table_name
                ),
            });
        }
        if !table_exists(connection, &declaration.table_name)? {
            return Err(ScanError::MissingMetatable {
                name: declaration.table_name.clone(),
            });
        }
        if !table_is_strict(connection, &declaration.table_name)? {
            return Err(ScanError::InvalidDeclaration {
                reason: format!(
                    "registered metatable `{}` is not STRICT",
                    declaration.table_name
                ),
            });
        }
    }

    for (name, kind) in reserved {
        if kind.id() != BOOTSTRAP_CATALOG && !registered.contains(name.as_str()) {
            return Err(ScanError::UnregisteredMetatable { name: name.clone() });
        }
    }
    Ok(())
}

fn table_exists(connection: &Connection, table: &str) -> Result<bool, ScanError> {
    connection
        .query_row(
            "SELECT 1 FROM sqlite_schema WHERE type = 'table' AND name = ?1",
            [table],
            |_| Ok(()),
        )
        .optional()
        .map(|row| row.is_some())
        .map_err(ScanError::sqlite)
}

fn table_is_strict(connection: &Connection, table: &str) -> Result<bool, ScanError> {
    connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [table],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map(|strict| strict == Some(1))
        .map_err(ScanError::sqlite)
}

type PhysicalColumn = (String, String, bool, u32);

fn table_columns(connection: &Connection, table: &str) -> Result<Vec<PhysicalColumn>, ScanError> {
    let sql = format!("PRAGMA main.table_info({})", quote_identifier(table));
    let mut statement = connection.prepare(&sql).map_err(ScanError::sqlite)?;
    statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)? != 0,
                row.get::<_, u32>(5)?,
            ))
        })
        .map_err(ScanError::sqlite)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(ScanError::sqlite)
}

pub(crate) fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;
    use covalence_lib_sqlite::{Connection, params};

    use super::{ScanError, scan_metatables};
    use crate::{
        BOOTSTRAP_CATALOG, MetatableKind, RUST_TYPES_INTERPRETATION_V0, RUST_TYPES_METATABLE_V0,
        metatable_name,
    };

    fn create_bootstrap(connection: &Connection) {
        let name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        connection
            .execute_batch(&format!(
                "CREATE TABLE \"{name}\" (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT;"
            ))
            .unwrap();
    }

    fn create_rust_types(connection: &Connection) {
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let rust_types = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
        connection
            .execute_batch(&format!(
                "CREATE TABLE \"{rust_types}\" (
                    id INTEGER PRIMARY KEY,
                    rust_type TEXT NOT NULL UNIQUE
                ) STRICT;"
            ))
            .unwrap();
        connection
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![rust_types, RUST_TYPES_INTERPRETATION_V0],
            )
            .unwrap();
    }

    #[test]
    fn ordinary_empty_database_has_no_bootstrap() {
        let connection = Connection::open_in_memory().unwrap();
        assert!(scan_metatables(&connection).unwrap().bootstrap().is_none());
    }

    #[test]
    fn empty_bootstrap_is_valid_candidate() {
        let connection = Connection::open_in_memory().unwrap();
        create_bootstrap(&connection);
        let candidate = scan_metatables(&connection).unwrap();
        assert!(candidate.bootstrap().unwrap().declarations().is_empty());
    }

    #[test]
    fn registered_extension_is_in_bootstrap_closure() {
        let connection = Connection::open_in_memory().unwrap();
        create_bootstrap(&connection);
        create_rust_types(&connection);
        let candidate = scan_metatables(&connection).unwrap();
        let [declaration] = candidate.bootstrap().unwrap().declarations() else {
            panic!("one declaration");
        };
        assert_eq!(declaration.interpretation(), RUST_TYPES_INTERPRETATION_V0);
    }

    #[test]
    fn extension_without_bootstrap_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        let name = metatable_name(MetatableKind::new(O256::from_bytes([7; 32])));
        connection
            .execute_batch(&format!("CREATE TABLE \"{name}\" (x INTEGER) STRICT;"))
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::UnregisteredMetatable { .. })
        ));
    }

    #[test]
    fn unregistered_extension_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        create_bootstrap(&connection);
        let name = metatable_name(MetatableKind::new(O256::from_bytes([7; 32])));
        connection
            .execute_batch(&format!("CREATE TABLE \"{name}\" (x INTEGER) STRICT;"))
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::UnregisteredMetatable { .. })
        ));
    }

    #[test]
    fn malformed_reserved_name_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute_batch("CREATE TABLE covalence_meta_nope (x INTEGER) STRICT;")
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::MalformedReservedName { .. })
        ));
    }

    #[test]
    fn missing_registered_extension_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        create_bootstrap(&connection);
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let missing = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
        connection
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![missing, RUST_TYPES_INTERPRETATION_V0],
            )
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::MissingMetatable { .. })
        ));
    }

    #[test]
    fn bootstrap_does_not_register_itself() {
        let connection = Connection::open_in_memory().unwrap();
        create_bootstrap(&connection);
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        connection
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, 'self')"
                ),
                [&bootstrap],
            )
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::InvalidDeclaration { .. })
        ));
    }
}
