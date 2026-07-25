use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, OptionalExtension};
use snafu::Snafu;

use crate::names::{
    INTEGER_BOOL_01_REPR_V0, META_PREFIX, MetatableKind, TABLE_SIGNATURE_CATALOG_V0,
    metatable_name, parse_metatable_name,
};

/// A structurally decoded, non-authoritative description of metatables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogCandidate {
    known: Vec<KnownMetatable>,
    unknown: Vec<UnknownMetatable>,
}

impl CatalogCandidate {
    /// Returns recognized, structurally validated metatables.
    #[must_use]
    pub fn known(&self) -> &[KnownMetatable] {
        &self.known
    }

    /// Returns well-formed metatable names whose kind is unknown.
    #[must_use]
    pub fn unknown(&self) -> &[UnknownMetatable] {
        &self.unknown
    }
}

/// A recognized metatable and its decoded rows.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KnownMetatable {
    /// The initial catalog assigning typed signatures to physical tables.
    TableSignatureCatalogV0(Vec<FieldDeclaration>),
}

/// A well-formed metatable name with semantics unknown to this build.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnknownMetatable {
    kind: MetatableKind,
    physical_name: String,
}

impl UnknownMetatable {
    /// Returns the unknown stable kind.
    #[must_use]
    pub const fn kind(&self) -> MetatableKind {
        self.kind
    }

    /// Returns the physical `SQLite` table name.
    #[must_use]
    pub fn physical_name(&self) -> &str {
        &self.physical_name
    }
}

/// One field in a claimed physical-table interpretation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FieldDeclaration {
    table_name: String,
    relation_id: O256,
    field_ordinal: u32,
    column_name: String,
    sort_id: O256,
    representation_id: O256,
}

impl FieldDeclaration {
    /// Returns the physical table name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table_name
    }

    /// Returns the logical relation identifier.
    #[must_use]
    pub const fn relation_id(&self) -> O256 {
        self.relation_id
    }

    /// Returns the zero-based field position.
    #[must_use]
    pub const fn field_ordinal(&self) -> u32 {
        self.field_ordinal
    }

    /// Returns the physical column name.
    #[must_use]
    pub fn column_name(&self) -> &str {
        &self.column_name
    }

    /// Returns the logical field sort.
    #[must_use]
    pub const fn sort_id(&self) -> O256 {
        self.sort_id
    }

    /// Returns the physical representation identifier.
    #[must_use]
    pub const fn representation_id(&self) -> O256 {
        self.representation_id
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
    /// The recognized bootstrap table had an unsupported physical shape.
    #[snafu(display("invalid table-signature catalog schema: {reason}"))]
    InvalidCatalogSchema {
        /// Stable rejection detail.
        reason: String,
    },
    /// A declaration row was malformed.
    #[snafu(display("invalid table-signature declaration: {reason}"))]
    InvalidDeclaration {
        /// Stable rejection detail.
        reason: String,
    },
    /// A declaration referenced a missing physical object.
    #[snafu(display("missing physical {object} `{name}`"))]
    MissingPhysicalObject {
        /// Object class.
        object: &'static str,
        /// Physical name.
        name: String,
    },
}

impl ScanError {
    fn sqlite(source: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite { source }
    }
}

/// Scans metatables over an arbitrary borrowed `SQLite` connection.
///
/// The result is a candidate only. This function performs no writes and makes
/// no claim about trust, grounding, completeness, or theorem authority.
///
/// # Errors
///
/// Rejects malformed reserved names, malformed recognized schemas or rows,
/// dangling physical references, and `SQLite` access failures.
pub fn scan_metatables(connection: &Connection) -> Result<CatalogCandidate, ScanError> {
    let mut statement = connection
        .prepare("SELECT name FROM sqlite_schema WHERE type = 'table' ORDER BY name")
        .map_err(ScanError::sqlite)?;
    let names = statement
        .query_map((), |row| row.get::<_, String>(0))
        .map_err(ScanError::sqlite)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(ScanError::sqlite)?;

    let mut known = Vec::new();
    let mut unknown = Vec::new();
    for name in names {
        if !name.starts_with(META_PREFIX) {
            continue;
        }
        let kind = parse_metatable_name(&name)
            .ok_or_else(|| ScanError::MalformedReservedName { name: name.clone() })?;
        if kind.id() == TABLE_SIGNATURE_CATALOG_V0 {
            if known
                .iter()
                .any(|item| matches!(item, KnownMetatable::TableSignatureCatalogV0(_)))
            {
                return Err(ScanError::InvalidCatalogSchema {
                    reason: String::from("multiple v0 catalogs"),
                });
            }
            let declarations = scan_table_signature_catalog(connection)?;
            known.push(KnownMetatable::TableSignatureCatalogV0(declarations));
        } else {
            unknown.push(UnknownMetatable {
                kind,
                physical_name: name,
            });
        }
    }

    Ok(CatalogCandidate { known, unknown })
}

fn scan_table_signature_catalog(
    connection: &Connection,
) -> Result<Vec<FieldDeclaration>, ScanError> {
    validate_catalog_schema(connection)?;
    let name = metatable_name(MetatableKind::new(TABLE_SIGNATURE_CATALOG_V0));
    let sql = format!(
        "SELECT table_name, relation_id, field_ordinal, column_name, sort_id, \
         representation_id FROM {} ORDER BY table_name, field_ordinal",
        quote_identifier(&name)
    );
    let mut statement = connection.prepare(&sql).map_err(ScanError::sqlite)?;
    let raw = statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, Vec<u8>>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, Vec<u8>>(4)?,
                row.get::<_, Vec<u8>>(5)?,
            ))
        })
        .map_err(ScanError::sqlite)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(ScanError::sqlite)?;

    let mut declarations = Vec::with_capacity(raw.len());
    for (table, relation, ordinal, column, sort, representation) in raw {
        let field_ordinal = u32::try_from(ordinal).map_err(|_| ScanError::InvalidDeclaration {
            reason: format!("field ordinal {ordinal} is outside u32"),
        })?;
        declarations.push(FieldDeclaration {
            table_name: table,
            relation_id: decode_o256("relation_id", &relation)?,
            field_ordinal,
            column_name: column,
            sort_id: decode_o256("sort_id", &sort)?,
            representation_id: decode_o256("representation_id", &representation)?,
        });
    }
    validate_declarations(connection, &declarations)?;
    Ok(declarations)
}

fn validate_catalog_schema(connection: &Connection) -> Result<(), ScanError> {
    let name = metatable_name(MetatableKind::new(TABLE_SIGNATURE_CATALOG_V0));
    let strict = connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [&name],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map_err(ScanError::sqlite)?;
    if strict != Some(1) {
        return Err(ScanError::InvalidCatalogSchema {
            reason: String::from("catalog must be a STRICT table in main"),
        });
    }

    let columns = table_columns(connection, &name)?;
    let expected = [
        ("table_name", "TEXT", true, 1_u32),
        ("relation_id", "BLOB", true, 0),
        ("field_ordinal", "INTEGER", true, 2),
        ("column_name", "TEXT", true, 0),
        ("sort_id", "BLOB", true, 0),
        ("representation_id", "BLOB", true, 0),
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
        return Err(ScanError::InvalidCatalogSchema {
            reason: String::from("columns do not match the v0 catalog contract"),
        });
    }
    Ok(())
}

fn validate_declarations(
    connection: &Connection,
    declarations: &[FieldDeclaration],
) -> Result<(), ScanError> {
    let mut tables: BTreeMap<&str, (O256, Vec<&FieldDeclaration>)> = BTreeMap::new();
    for declaration in declarations {
        let entry = tables
            .entry(&declaration.table_name)
            .or_insert_with(|| (declaration.relation_id, Vec::new()));
        if entry.0 != declaration.relation_id {
            return Err(ScanError::InvalidDeclaration {
                reason: format!(
                    "table `{}` has more than one relation ID",
                    declaration.table_name
                ),
            });
        }
        entry.1.push(declaration);
    }

    let mut relations = BTreeSet::new();
    for (table, (relation, fields)) in tables {
        if !relations.insert(relation) {
            return Err(ScanError::InvalidDeclaration {
                reason: format!("relation {relation} is assigned to more than one table"),
            });
        }
        let columns = table_columns(connection, table)?;
        if columns.is_empty() {
            return Err(ScanError::MissingPhysicalObject {
                object: "table",
                name: table.to_owned(),
            });
        }
        if !table_is_strict(connection, table)? {
            return Err(ScanError::InvalidDeclaration {
                reason: format!("interpreted table `{table}` is not STRICT"),
            });
        }
        for (expected, field) in fields.iter().enumerate() {
            if usize::try_from(field.field_ordinal) != Ok(expected) {
                return Err(ScanError::InvalidDeclaration {
                    reason: format!("table `{table}` has non-contiguous field ordinals"),
                });
            }
            let physical = columns
                .iter()
                .find(|(name, _, _, _)| name == &field.column_name)
                .ok_or_else(|| ScanError::MissingPhysicalObject {
                    object: "column",
                    name: format!("{table}.{}", field.column_name),
                })?;
            if !physical.2 {
                return Err(ScanError::InvalidDeclaration {
                    reason: format!(
                        "interpreted column `{table}.{}` is nullable",
                        field.column_name
                    ),
                });
            }
            if field.representation_id == INTEGER_BOOL_01_REPR_V0 && physical.1 != "INTEGER" {
                return Err(ScanError::InvalidDeclaration {
                    reason: format!(
                        "Bool column `{table}.{}` is declared as {} rather than INTEGER",
                        field.column_name, physical.1
                    ),
                });
            }
        }
    }
    Ok(())
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

fn decode_o256(field: &str, bytes: &[u8]) -> Result<O256, ScanError> {
    let exact: [u8; 32] = bytes
        .try_into()
        .map_err(|_| ScanError::InvalidDeclaration {
            reason: format!("{field} must contain exactly 32 bytes"),
        })?;
    Ok(O256::from_bytes(exact))
}

pub(crate) fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;
    use covalence_lib_sqlite::{Connection, params};

    use super::{KnownMetatable, ScanError, scan_metatables};
    use crate::{
        BOOL_SORT_V0, BOOL_VALUES_RELATION_V0, INTEGER_BOOL_01_REPR_V0, MetatableKind,
        TABLE_SIGNATURE_CATALOG_V0, metatable_name,
    };

    fn create_catalog(connection: &Connection) {
        let name = metatable_name(MetatableKind::new(TABLE_SIGNATURE_CATALOG_V0));
        connection
            .execute_batch(&format!(
                "CREATE TABLE \"{name}\" (
                    table_name TEXT NOT NULL,
                    relation_id BLOB NOT NULL CHECK (length(relation_id) = 32),
                    field_ordinal INTEGER NOT NULL CHECK (field_ordinal >= 0),
                    column_name TEXT NOT NULL,
                    sort_id BLOB NOT NULL CHECK (length(sort_id) = 32),
                    representation_id BLOB NOT NULL CHECK (length(representation_id) = 32),
                    PRIMARY KEY (table_name, field_ordinal),
                    UNIQUE (table_name, column_name)
                ) STRICT;
                CREATE TABLE bool_values (
                    value INTEGER NOT NULL CHECK (value IN (0, 1)),
                    UNIQUE (value)
                ) STRICT;"
            ))
            .unwrap();
        connection
            .execute(
                &format!(
                    "INSERT INTO \"{name}\" (
                        table_name, relation_id, field_ordinal, column_name,
                        sort_id, representation_id
                    ) VALUES (?1, ?2, 0, ?3, ?4, ?5)"
                ),
                params![
                    "bool_values",
                    BOOL_VALUES_RELATION_V0.as_bytes().as_slice(),
                    "value",
                    BOOL_SORT_V0.as_bytes().as_slice(),
                    INTEGER_BOOL_01_REPR_V0.as_bytes().as_slice(),
                ],
            )
            .unwrap();
    }

    #[test]
    fn empty_database_has_empty_candidate() {
        let connection = Connection::open_in_memory().unwrap();
        let candidate = scan_metatables(&connection).unwrap();
        assert!(candidate.known().is_empty());
        assert!(candidate.unknown().is_empty());
    }

    #[test]
    fn known_catalog_is_decoded_without_trust() {
        let connection = Connection::open_in_memory().unwrap();
        create_catalog(&connection);
        let candidate = scan_metatables(&connection).unwrap();
        let [KnownMetatable::TableSignatureCatalogV0(fields)] = candidate.known() else {
            panic!("one known catalog");
        };
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].table_name(), "bool_values");
        assert_eq!(fields[0].sort_id(), BOOL_SORT_V0);
    }

    #[test]
    fn unknown_kind_is_retained_opaquely() {
        let connection = Connection::open_in_memory().unwrap();
        let unknown = O256::from_bytes([7; 32]);
        let name = metatable_name(MetatableKind::new(unknown));
        connection
            .execute_batch(&format!("CREATE TABLE \"{name}\" (x INTEGER) STRICT;"))
            .unwrap();
        let candidate = scan_metatables(&connection).unwrap();
        assert!(candidate.known().is_empty());
        assert_eq!(candidate.unknown()[0].kind().id(), unknown);
    }

    #[test]
    fn malformed_reserved_name_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute_batch("CREATE TABLE \"covalence.meta.nope\" (x INTEGER) STRICT;")
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::MalformedReservedName { .. })
        ));
    }

    #[test]
    fn dangling_column_fails_closed() {
        let connection = Connection::open_in_memory().unwrap();
        create_catalog(&connection);
        let name = metatable_name(MetatableKind::new(TABLE_SIGNATURE_CATALOG_V0));
        connection
            .execute(
                &format!("UPDATE \"{name}\" SET column_name = 'missing'"),
                (),
            )
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::MissingPhysicalObject {
                object: "column",
                ..
            })
        ));
    }

    #[test]
    fn interpreted_tables_must_be_strict() {
        let connection = Connection::open_in_memory().unwrap();
        create_catalog(&connection);
        connection
            .execute_batch(
                "ALTER TABLE bool_values RENAME TO old_bool_values;
                 CREATE TABLE bool_values (
                    value INTEGER NOT NULL CHECK (value IN (0, 1)),
                    UNIQUE (value)
                 );",
            )
            .unwrap();
        assert!(matches!(
            scan_metatables(&connection),
            Err(ScanError::InvalidDeclaration { .. })
        ));
    }
}
