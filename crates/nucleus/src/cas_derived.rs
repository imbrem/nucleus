use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use crate::{CasObjectId, CasTable, Connection, cas_table, catalog};

pub(crate) const KEYED_INTERPRETATION: &str = "cov.cas.blake3-keyed/v0";
pub(crate) const CONTEXT_INTERPRETATION: &str = "cov.cas.blake3-context/v0";

/// A checked keyed-BLAKE3 representation of a CAS object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyedObject {
    /// Table-local object identity in the target CAS.
    pub id: CasObjectId,
    /// BLAKE3 key.
    pub key: O256,
    /// Bytes hashed under `key`.
    pub bytes: Vec<u8>,
}

/// A checked BLAKE3 derive-key-context representation of a CAS object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextObject {
    /// Table-local object identity in the target CAS.
    pub id: CasObjectId,
    /// Human-readable BLAKE3 derive-key context.
    pub context: String,
    /// Bytes hashed under `context`.
    pub bytes: Vec<u8>,
}

/// An auxiliary table representing CAS objects by keyed-BLAKE3 preimages.
#[derive(Debug)]
pub struct KeyedObjects<'conn> {
    connection: &'conn Connection,
    name: String,
    cas_table: String,
}

impl KeyedObjects<'_> {
    /// Returns the auxiliary table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the target CAS table named by the foreign key.
    #[must_use]
    pub fn cas_table(&self) -> &str {
        &self.cas_table
    }

    /// Declares a keyed object in the target CAS and records its preimage.
    ///
    /// The base CAS row remains unresolved: its ordinary unkeyed `data`
    /// column is not the representation used by this object.
    ///
    /// # Errors
    ///
    /// Returns an error for cross-connection wrappers, occupied ordinary
    /// objects, inconsistent preimages, or `SQLite` failures.
    pub fn insert(
        &self,
        cas: &CasTable<'_>,
        key: O256,
        bytes: &[u8],
    ) -> Result<CasObjectId, DerivedObjectError> {
        self.check_target(cas)?;
        let hash = O256::with_key(&key, bytes);
        let transaction = self
            .connection
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(InsertSnafu)?;
        let id = cas.declare(hash).context(CasSnafu)?;
        ensure_unresolved(cas, id, &self.name)?;
        let changed = transaction
            .execute(
                &format!(
                    "INSERT INTO {} (object_id, key, bytes) VALUES (?1, ?2, ?3)
                     ON CONFLICT (object_id) DO UPDATE SET
                        key = excluded.key,
                        bytes = excluded.bytes
                     WHERE key = excluded.key AND bytes = excluded.bytes",
                    catalog::main_table(&self.name)
                ),
                (id.get(), key.as_ref(), bytes),
            )
            .context(InsertSnafu)?;
        if changed == 0 {
            return Err(DerivedObjectError::ConflictingPreimage { id });
        }
        transaction.commit().context(InsertSnafu)?;
        Ok(id)
    }

    /// Loads and revalidates all keyed representations.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid target meaning, foreign keys, addresses,
    /// occupied ordinary objects, false preimages, or `SQLite` failures.
    pub fn objects(&self) -> Result<Vec<KeyedObject>, DerivedObjectError> {
        validate_keyed(self.connection.neutron.sqlite(), &self.name).map(|(_, objects)| objects)
    }

    fn check_target(&self, cas: &CasTable<'_>) -> Result<(), DerivedObjectError> {
        if !std::ptr::eq(cas.connection, self.connection) {
            return Err(DerivedObjectError::DifferentConnection);
        }
        if cas.name() != self.cas_table {
            return Err(DerivedObjectError::WrongTarget {
                expected: self.cas_table.clone(),
                actual: cas.name().to_owned(),
            });
        }
        Ok(())
    }
}

/// An auxiliary table representing CAS objects by BLAKE3 context preimages.
#[derive(Debug)]
pub struct ContextObjects<'conn> {
    connection: &'conn Connection,
    name: String,
    cas_table: String,
}

impl ContextObjects<'_> {
    /// Returns the auxiliary table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the target CAS table named by the foreign key.
    #[must_use]
    pub fn cas_table(&self) -> &str {
        &self.cas_table
    }

    /// Declares a context-derived object and records its preimage.
    ///
    /// # Errors
    ///
    /// Returns an error for cross-connection wrappers, occupied ordinary
    /// objects, inconsistent preimages, or `SQLite` failures.
    pub fn insert(
        &self,
        cas: &CasTable<'_>,
        context: &str,
        bytes: &[u8],
    ) -> Result<CasObjectId, DerivedObjectError> {
        self.check_target(cas)?;
        let hash = O256::with_key(context, bytes);
        let transaction = self
            .connection
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(InsertSnafu)?;
        let id = cas.declare(hash).context(CasSnafu)?;
        ensure_unresolved(cas, id, &self.name)?;
        let changed = transaction
            .execute(
                &format!(
                    "INSERT INTO {} (object_id, context, bytes) VALUES (?1, ?2, ?3)
                     ON CONFLICT (object_id) DO UPDATE SET
                        context = excluded.context,
                        bytes = excluded.bytes
                     WHERE context = excluded.context AND bytes = excluded.bytes",
                    catalog::main_table(&self.name)
                ),
                (id.get(), context, bytes),
            )
            .context(InsertSnafu)?;
        if changed == 0 {
            return Err(DerivedObjectError::ConflictingPreimage { id });
        }
        transaction.commit().context(InsertSnafu)?;
        Ok(id)
    }

    /// Loads and revalidates all context-derived representations.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid target meaning, foreign keys, addresses,
    /// occupied ordinary objects, false preimages, or `SQLite` failures.
    pub fn objects(&self) -> Result<Vec<ContextObject>, DerivedObjectError> {
        validate_context(self.connection.neutron.sqlite(), &self.name).map(|(_, objects)| objects)
    }

    fn check_target(&self, cas: &CasTable<'_>) -> Result<(), DerivedObjectError> {
        if !std::ptr::eq(cas.connection, self.connection) {
            return Err(DerivedObjectError::DifferentConnection);
        }
        if cas.name() != self.cas_table {
            return Err(DerivedObjectError::WrongTarget {
                expected: self.cas_table.clone(),
                actual: cas.name().to_owned(),
            });
        }
        Ok(())
    }
}

impl Connection {
    /// Discovers every interpreted keyed-object table.
    ///
    /// # Errors
    ///
    /// Returns an error when catalog, target CAS, schema, or preimages are
    /// invalid.
    pub fn keyed_object_tables(&self) -> Result<Vec<KeyedObjects<'_>>, DerivedObjectError> {
        catalog::entries(self.neutron.sqlite())
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == KEYED_INTERPRETATION)
            .map(|entry| {
                let (cas_table, _) = validate_keyed(self.neutron.sqlite(), &entry.table)?;
                Ok(KeyedObjects {
                    connection: self,
                    name: entry.table,
                    cas_table,
                })
            })
            .collect()
    }

    /// Discovers every interpreted context-object table.
    ///
    /// # Errors
    ///
    /// Returns an error when catalog, target CAS, schema, or preimages are
    /// invalid.
    pub fn context_object_tables(&self) -> Result<Vec<ContextObjects<'_>>, DerivedObjectError> {
        catalog::entries(self.neutron.sqlite())
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == CONTEXT_INTERPRETATION)
            .map(|entry| {
                let (cas_table, _) = validate_context(self.neutron.sqlite(), &entry.table)?;
                Ok(ContextObjects {
                    connection: self,
                    name: entry.table,
                    cas_table,
                })
            })
            .collect()
    }
}

pub(crate) fn create_keyed_table(
    sqlite: &sqlite::Connection,
    name: &str,
    cas_table: &str,
) -> sqlite::Result<()> {
    sqlite.execute_batch(&format!(
        "CREATE TABLE {} (
            object_id INTEGER PRIMARY KEY
                REFERENCES {} (object_id),
            key BLOB NOT NULL CHECK (length(key) = 32),
            bytes BLOB NOT NULL
        ) STRICT;",
        catalog::main_table(name),
        catalog::quote_identifier(cas_table)
    ))
}

pub(crate) fn create_context_table(
    sqlite: &sqlite::Connection,
    name: &str,
    cas_table: &str,
) -> sqlite::Result<()> {
    sqlite.execute_batch(&format!(
        "CREATE TABLE {} (
            object_id INTEGER PRIMARY KEY
                REFERENCES {} (object_id),
            context TEXT NOT NULL,
            bytes BLOB NOT NULL
        ) STRICT;",
        catalog::main_table(name),
        catalog::quote_identifier(cas_table)
    ))
}

pub(crate) fn keyed_wrapper<'conn>(
    connection: &'conn Connection,
    name: &str,
    cas_table: &str,
) -> KeyedObjects<'conn> {
    KeyedObjects {
        connection,
        name: name.to_owned(),
        cas_table: cas_table.to_owned(),
    }
}

pub(crate) fn context_wrapper<'conn>(
    connection: &'conn Connection,
    name: &str,
    cas_table: &str,
) -> ContextObjects<'conn> {
    ContextObjects {
        connection,
        name: name.to_owned(),
        cas_table: cas_table.to_owned(),
    }
}

pub(crate) fn validate_keyed(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<(String, Vec<KeyedObject>), DerivedObjectError> {
    let target = validate_shape(
        sqlite,
        name,
        &[
            (String::from("object_id"), String::from("INTEGER"), false, 1),
            (String::from("key"), String::from("BLOB"), true, 0),
            (String::from("bytes"), String::from("BLOB"), true, 0),
        ],
    )?;
    let rows = sqlite
        .prepare(&format!(
            "SELECT object_id, key, bytes FROM {} ORDER BY object_id",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok((
                CasObjectId(row.get::<_, i64>(0)?),
                row.get::<_, Vec<u8>>(1)?,
                row.get::<_, Vec<u8>>(2)?,
            ))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    let mut objects = Vec::with_capacity(rows.len());
    for (id, key, bytes) in rows {
        let key = <[u8; 32]>::try_from(key)
            .map(O256::from_array)
            .map_err(|_| DerivedObjectError::MalformedKey {
                table: name.to_owned(),
            })?;
        validate_preimage(sqlite, name, &target, id, O256::with_key(&key, &bytes))?;
        objects.push(KeyedObject { id, key, bytes });
    }
    Ok((target, objects))
}

pub(crate) fn validate_context(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<(String, Vec<ContextObject>), DerivedObjectError> {
    let target = validate_shape(
        sqlite,
        name,
        &[
            (String::from("object_id"), String::from("INTEGER"), false, 1),
            (String::from("context"), String::from("TEXT"), true, 0),
            (String::from("bytes"), String::from("BLOB"), true, 0),
        ],
    )?;
    let rows = sqlite
        .prepare(&format!(
            "SELECT object_id, context, bytes FROM {} ORDER BY object_id",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok((
                CasObjectId(row.get::<_, i64>(0)?),
                row.get::<_, String>(1)?,
                row.get::<_, Vec<u8>>(2)?,
            ))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    let mut objects = Vec::with_capacity(rows.len());
    for (id, context, bytes) in rows {
        validate_preimage(
            sqlite,
            name,
            &target,
            id,
            O256::with_key(context.as_str(), &bytes),
        )?;
        objects.push(ContextObject { id, context, bytes });
    }
    Ok((target, objects))
}

fn validate_shape(
    sqlite: &sqlite::Connection,
    name: &str,
    columns: &[(String, String, bool, i64); 3],
) -> Result<String, DerivedObjectError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)? != *columns
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, false)
    {
        return Err(DerivedObjectError::MalformedTable {
            table: name.to_owned(),
        });
    }
    let [foreign_key] = catalog::foreign_keys(sqlite, name)
        .context(ScanSnafu)?
        .try_into()
        .map_err(|_| DerivedObjectError::MalformedForeignKey {
            table: name.to_owned(),
        })?;
    if foreign_key.from != "object_id"
        || foreign_key.to != "object_id"
        || foreign_key.on_update != "NO ACTION"
        || foreign_key.on_delete != "NO ACTION"
    {
        return Err(DerivedObjectError::MalformedForeignKey {
            table: name.to_owned(),
        });
    }

    let target = foreign_key.table;
    let meanings = catalog::entries(sqlite).map_err(map_catalog_error)?;
    if meanings
        .iter()
        .find(|entry| entry.table == target)
        .map(|entry| entry.interpretation.as_str())
        != Some(cas_table::INTERPRETATION)
    {
        return Err(DerivedObjectError::WrongTargetMeaning {
            table: name.to_owned(),
            target,
        });
    }
    cas_table::validate_table(sqlite, &target).context(CasSnafu)?;
    Ok(target)
}

fn validate_preimage(
    sqlite: &sqlite::Connection,
    table: &str,
    target: &str,
    id: CasObjectId,
    actual: O256,
) -> Result<(), DerivedObjectError> {
    let (expected, data) = cas_table::entry(sqlite, target, id)
        .context(CasSnafu)?
        .ok_or_else(|| DerivedObjectError::MissingObject {
            table: table.to_owned(),
            target: target.to_owned(),
            id,
        })?;
    if data.is_some() {
        return Err(DerivedObjectError::OccupiedObject {
            table: table.to_owned(),
            target: target.to_owned(),
            id,
        });
    }
    if actual != expected {
        return Err(DerivedObjectError::FalsePreimage {
            table: table.to_owned(),
            target: target.to_owned(),
            id,
            expected,
            actual,
        });
    }
    Ok(())
}

fn ensure_unresolved(
    cas: &CasTable<'_>,
    id: CasObjectId,
    table: &str,
) -> Result<(), DerivedObjectError> {
    if cas.fetch_id(id).context(CasSnafu)?.is_some() {
        return Err(DerivedObjectError::OccupiedObject {
            table: table.to_owned(),
            target: cas.name.clone(),
            id,
        });
    }
    Ok(())
}

fn map_catalog_error(error: crate::CatalogError) -> DerivedObjectError {
    match error {
        crate::CatalogError::Sqlite { source } => DerivedObjectError::Catalog { source },
        source => DerivedObjectError::InvalidCatalog { source },
    }
}

/// Failure to construct, validate, or use a derived CAS representation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DerivedObjectError {
    /// Wrappers from different Nucleus connections were combined.
    #[snafu(display("derived-object and target wrappers belong to different connections"))]
    DifferentConnection,

    /// A wrapper was used with a different connection or target CAS.
    #[snafu(display("expected CAS table {expected:?}, got {actual:?}"))]
    WrongTarget {
        /// Required target.
        expected: String,
        /// Supplied target.
        actual: String,
    },

    /// The persistent catalog is invalid.
    #[snafu(display("{source}"))]
    InvalidCatalog {
        /// Underlying failure.
        source: crate::CatalogError,
    },

    /// The persistent catalog could not be read.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An auxiliary table has incompatible geometry.
    #[snafu(display("derived-object table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// An auxiliary table does not have exactly the required CAS foreign key.
    #[snafu(display("derived-object table {table:?} has an incompatible foreign key"))]
    MalformedForeignKey {
        /// Physical table.
        table: String,
    },

    /// The foreign-key target is not interpreted as a CAS.
    #[snafu(display("derived-object table {table:?} targets non-CAS table {target:?}"))]
    WrongTargetMeaning {
        /// Auxiliary table.
        table: String,
        /// Rejected target.
        target: String,
    },

    /// A keyed row contains a malformed key.
    #[snafu(display("derived-object table {table:?} contains a malformed BLAKE3 key"))]
    MalformedKey {
        /// Physical table.
        table: String,
    },

    /// An auxiliary row references a missing CAS identity.
    #[snafu(display(
        "derived-object table {table:?} references missing object {} in {target:?}",
        id.get()
    ))]
    MissingObject {
        /// Auxiliary table.
        table: String,
        /// Target CAS.
        target: String,
        /// Missing identity.
        id: CasObjectId,
    },

    /// An auxiliary representation conflicts with resident ordinary bytes.
    #[snafu(display(
        "derived-object table {table:?} references ordinary resident object {} in {target:?}",
        id.get()
    ))]
    OccupiedObject {
        /// Auxiliary table.
        table: String,
        /// Target CAS.
        target: String,
        /// Occupied identity.
        id: CasObjectId,
    },

    /// A preimage does not produce the CAS row's stable address.
    #[snafu(display(
        "derived-object table {table:?} computes {actual} for object {} in {target:?}, expected {expected}",
        id.get()
    ))]
    FalsePreimage {
        /// Auxiliary table.
        table: String,
        /// Target CAS.
        target: String,
        /// Object identity.
        id: CasObjectId,
        /// CAS address.
        expected: O256,
        /// Computed address.
        actual: O256,
    },

    /// A CAS object already has a different preimage in this representation.
    #[snafu(display("object {} already has a conflicting derived preimage", id.get()))]
    ConflictingPreimage {
        /// Object identity.
        id: CasObjectId,
    },

    /// A derived row could not be inserted.
    #[snafu(display("could not insert derived CAS object: {source}"))]
    Insert {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An auxiliary table could not be scanned.
    #[snafu(display("could not scan derived CAS objects: {source}"))]
    Scan {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// A target CAS operation failed.
    #[snafu(display("could not validate target CAS: {source}"))]
    Cas {
        /// Underlying failure.
        source: crate::CasTableError,
    },
}
