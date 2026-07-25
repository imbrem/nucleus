use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, params};
use covalence_neutron::{
    BOOL_SORT_V0, BOOL_VALUES_RELATION_V0, CatalogCandidate, FieldDeclaration,
    INTEGER_BOOL_01_REPR_V0, KnownMetatable, MetatableKind, ScanError, TABLE_SIGNATURE_CATALOG_V0,
    metatable_name, scan_metatables,
};
use snafu::Snafu;

/// One accepted field in a relation signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FieldSignature {
    name: String,
    sort: O256,
}

impl FieldSignature {
    /// Returns the physical field name used by this interpretation.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the logical sort identifier.
    #[must_use]
    pub const fn sort(&self) -> O256 {
        self.sort
    }
}

/// One accepted logical relation signature.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationSignature {
    id: O256,
    fields: Vec<FieldSignature>,
}

impl RelationSignature {
    /// Returns the stable logical relation identifier.
    #[must_use]
    pub const fn id(&self) -> O256 {
        self.id
    }

    /// Returns the ordered fields.
    #[must_use]
    pub fn fields(&self) -> &[FieldSignature] {
        &self.fields
    }
}

/// A validated mapping from one physical table to a logical relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TableInterpretation {
    table_name: String,
    column_name: String,
    representation: O256,
    signature: RelationSignature,
}

impl TableInterpretation {
    /// Returns the physical table name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table_name
    }

    /// Returns the accepted logical signature.
    #[must_use]
    pub const fn signature(&self) -> &RelationSignature {
        &self.signature
    }
}

/// Accepted connection-local relation interpretations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NeutronCatalog {
    interpretations: Vec<TableInterpretation>,
}

impl NeutronCatalog {
    /// Returns accepted interpretations.
    #[must_use]
    pub fn interpretations(&self) -> &[TableInterpretation] {
        &self.interpretations
    }

    fn accept(candidate: &CatalogCandidate) -> Result<Self, CatalogError> {
        let declarations = match candidate.known() {
            [KnownMetatable::TableSignatureCatalogV0(declarations)] => declarations,
            [] => return Err(CatalogError::MissingBootstrapCatalog),
            _ => return Err(CatalogError::ConflictingBootstrapCatalogs),
        };
        let [declaration] = declarations.as_slice() else {
            return Err(CatalogError::UnsupportedCatalog {
                reason: String::from("v0 requires exactly one interpreted Bool field"),
            });
        };
        validate_bool_declaration(declaration)?;
        Ok(Self {
            interpretations: vec![TableInterpretation {
                table_name: declaration.table_name().to_owned(),
                column_name: declaration.column_name().to_owned(),
                representation: declaration.representation_id(),
                signature: RelationSignature {
                    id: declaration.relation_id(),
                    fields: vec![FieldSignature {
                        name: declaration.column_name().to_owned(),
                        sort: declaration.sort_id(),
                    }],
                },
            }],
        })
    }

    fn relation(&self, id: O256) -> Option<&TableInterpretation> {
        self.interpretations
            .iter()
            .find(|interpretation| interpretation.signature.id == id)
    }
}

fn validate_bool_declaration(declaration: &FieldDeclaration) -> Result<(), CatalogError> {
    if declaration.relation_id() != BOOL_VALUES_RELATION_V0
        || declaration.field_ordinal() != 0
        || declaration.sort_id() != BOOL_SORT_V0
        || declaration.representation_id() != INTEGER_BOOL_01_REPR_V0
    {
        return Err(CatalogError::UnsupportedCatalog {
            reason: String::from("declaration is not the built-in Bool relation signature"),
        });
    }
    Ok(())
}

/// Rejection while accepting structurally decoded metadata as a known API.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum CatalogError {
    /// The required bootstrap catalog was absent.
    #[snafu(display("missing v0 table-signature catalog"))]
    MissingBootstrapCatalog,
    /// More than one recognized bootstrap catalog was supplied.
    #[snafu(display("conflicting bootstrap catalogs"))]
    ConflictingBootstrapCatalogs,
    /// The catalog claims semantics this build does not recognize.
    #[snafu(display("unsupported catalog: {reason}"))]
    UnsupportedCatalog {
        /// Stable reason.
        reason: String,
    },
}

/// The only writable trusted `SQLite` owner in this initial slice.
///
/// The raw connection is intentionally private and has no public escape hatch.
pub struct TrustedDb {
    connection: Connection,
    catalog: NeutronCatalog,
    generation: u64,
}

impl TrustedDb {
    /// Creates a fresh, uniquely owned in-memory trusted database.
    ///
    /// # Errors
    ///
    /// Fails atomically if `SQLite` setup, metatable scanning, or catalog
    /// acceptance fails.
    pub fn create_in_memory() -> Result<Self, TrustedDbError> {
        let mut connection = Connection::open_in_memory().map_err(TrustedDbError::sqlite)?;
        connection
            .execute_batch("PRAGMA foreign_keys = ON;")
            .map_err(TrustedDbError::sqlite)?;
        let transaction = connection.transaction().map_err(TrustedDbError::sqlite)?;
        let metatable = metatable_name(MetatableKind::new(TABLE_SIGNATURE_CATALOG_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{metatable}\" (
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
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{metatable}\" (
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
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog = NeutronCatalog::accept(&candidate).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        Ok(Self {
            connection,
            catalog,
            generation: 0,
        })
    }

    /// Returns the accepted connection-local catalog.
    #[must_use]
    pub const fn catalog(&self) -> &NeutronCatalog {
        &self.catalog
    }

    /// Returns the schema generation.
    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    /// Resolves the recognized Bool relation as a checked mutable capability.
    ///
    /// # Errors
    ///
    /// Rejects unknown relations and catalog entries whose signature or
    /// representation is not the built-in Bool relation.
    pub fn bool_relation(&mut self, relation: O256) -> Result<BoolRelation<'_>, TrustedDbError> {
        let interpretation = self
            .catalog
            .relation(relation)
            .filter(|interpretation| {
                interpretation.representation == INTEGER_BOOL_01_REPR_V0
                    && interpretation.signature.fields.as_slice()
                        == [FieldSignature {
                            name: interpretation.column_name.clone(),
                            sort: BOOL_SORT_V0,
                        }]
            })
            .cloned()
            .ok_or(TrustedDbError::UnknownBoolRelation { relation })?;
        Ok(BoolRelation {
            connection: &mut self.connection,
            interpretation,
        })
    }
}

/// Result of inserting into a logical set relation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum InsertOutcome {
    /// A new logical element was inserted.
    Inserted,
    /// The logical set already contained the element.
    AlreadyPresent,
}

/// Checked mutable access to one recognized `Bool` set relation.
pub struct BoolRelation<'db> {
    connection: &'db mut Connection,
    interpretation: TableInterpretation,
}

impl BoolRelation<'_> {
    /// Inserts one Bool using the accepted representation.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the checked SQL operation fails.
    pub fn insert(&mut self, value: bool) -> Result<InsertOutcome, TrustedDbError> {
        let table = quote_identifier(&self.interpretation.table_name);
        let column = quote_identifier(&self.interpretation.column_name);
        let changed = self
            .connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} ({column}) VALUES (?1)"),
                [i64::from(value)],
            )
            .map_err(TrustedDbError::sqlite)?;
        Ok(if changed == 0 {
            InsertOutcome::AlreadyPresent
        } else {
            InsertOutcome::Inserted
        })
    }

    /// Reads and decodes the logical set in deterministic order.
    ///
    /// # Errors
    ///
    /// Rejects `SQLite` values outside the accepted `INTEGER` 0/1 representation.
    pub fn values(&self) -> Result<Vec<bool>, TrustedDbError> {
        let table = quote_identifier(&self.interpretation.table_name);
        let column = quote_identifier(&self.interpretation.column_name);
        let mut statement = self
            .connection
            .prepare(&format!("SELECT {column} FROM {table} ORDER BY {column}"))
            .map_err(TrustedDbError::sqlite)?;
        let values = statement
            .query_map((), |row| row.get::<_, i64>(0))
            .map_err(TrustedDbError::sqlite)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(TrustedDbError::sqlite)?;
        values
            .into_iter()
            .map(|value| match value {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err(TrustedDbError::InvalidBoolValue { value }),
            })
            .collect()
    }
}

/// Failure while constructing or using the exclusive trusted wrapper.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum TrustedDbError {
    /// `SQLite` failed within a checked operation.
    #[snafu(display("trusted SQLite operation failed: {source}"))]
    Sqlite {
        /// Underlying failure.
        source: covalence_lib_sqlite::Error,
    },
    /// Mechanical metatable scanning failed.
    #[snafu(display("could not scan metatables: {source}"))]
    Scan {
        /// Scanner failure.
        source: ScanError,
    },
    /// Structurally valid metadata was not accepted by compiled policy.
    #[snafu(display("could not accept Neutron catalog: {source}"))]
    Catalog {
        /// Acceptance failure.
        source: CatalogError,
    },
    /// No accepted Bool relation had the requested identity.
    #[snafu(display("unknown or incompatible Bool relation {relation}"))]
    UnknownBoolRelation {
        /// Requested stable relation ID.
        relation: O256,
    },
    /// Stored data violated the accepted representation.
    #[snafu(display("invalid SQLite INTEGER Bool value {value}"))]
    InvalidBoolValue {
        /// Invalid integer.
        value: i64,
    },
}

impl TrustedDbError {
    fn sqlite(source: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite { source }
    }

    const fn scan(source: ScanError) -> Self {
        Self::Scan { source }
    }

    const fn catalog(source: CatalogError) -> Self {
        Self::Catalog { source }
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;
    use covalence_neutron::{BOOL_VALUES_RELATION_V0, TABLE_SIGNATURE_CATALOG_V0};

    use super::{InsertOutcome, TrustedDb, TrustedDbError};

    #[test]
    fn creation_rescans_and_accepts_the_bootstrap_catalog() {
        let database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(database.generation(), 0);
        assert_eq!(database.catalog().interpretations().len(), 1);
        assert_eq!(
            database.catalog().interpretations()[0].signature().id(),
            BOOL_VALUES_RELATION_V0
        );
        assert_ne!(
            database.catalog().interpretations()[0].signature().id(),
            TABLE_SIGNATURE_CATALOG_V0
        );
    }

    #[test]
    fn bool_writes_are_typed_and_set_valued() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        let mut relation = database.bool_relation(BOOL_VALUES_RELATION_V0).unwrap();
        assert_eq!(relation.insert(true).unwrap(), InsertOutcome::Inserted);
        assert_eq!(
            relation.insert(true).unwrap(),
            InsertOutcome::AlreadyPresent
        );
        assert_eq!(relation.insert(false).unwrap(), InsertOutcome::Inserted);
        assert_eq!(relation.values().unwrap(), vec![false, true]);
    }

    #[test]
    fn unknown_relation_cannot_construct_bool_capability() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.bool_relation(O256::from_bytes([0; 32])),
            Err(TrustedDbError::UnknownBoolRelation { .. })
        ));
    }
}
