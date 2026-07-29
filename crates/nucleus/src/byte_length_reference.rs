use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use crate::{CasTable, Connection, cas_table, catalog};

pub(crate) const INTERPRETATION: &str = "cov.bytes.length-reference/v0";

/// A checked byte-length statement resolved through a persistent CAS.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteLengthReference {
    /// Interpreted CAS table containing the ordinary bytes.
    pub cas_table: String,
    /// Stable content address of the bytes.
    pub hash: O256,
    /// Checked number of bytes.
    pub length: u64,
}

/// A validated relation of cross-table byte-length statements.
///
/// Durable references use `(cas_table, hash)`, not the target table's local
/// integer ID. The latter is only a resolution optimization.
#[derive(Debug)]
pub struct ByteLengthReferences<'conn> {
    connection: &'conn Connection,
    name: String,
}

impl ByteLengthReferences<'_> {
    /// Returns the physical child table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Stores bytes in `cas` and records their checked length.
    ///
    /// # Errors
    ///
    /// Returns an error when wrappers belong to different connections, the
    /// length cannot be represented, or either relation cannot be updated.
    pub fn record(
        &self,
        cas: &CasTable<'_>,
        data: &[u8],
    ) -> Result<ByteLengthReference, ByteLengthReferenceError> {
        if !std::ptr::eq(cas.connection, self.connection) {
            return Err(ByteLengthReferenceError::DifferentConnection);
        }
        let length =
            u64::try_from(data.len()).map_err(|_| ByteLengthReferenceError::LengthOutOfRange)?;
        let sqlite_length =
            i64::try_from(length).map_err(|_| ByteLengthReferenceError::LengthOutOfRange)?;
        let hash = cas.store(data).context(CasSnafu)?;
        let changed = self
            .connection
            .neutron
            .sqlite()
            .execute(
                &format!(
                    "INSERT INTO {} (cas_table, hash, byte_length) VALUES (?1, ?2, ?3)
                     ON CONFLICT (cas_table, hash) DO UPDATE SET
                        byte_length = excluded.byte_length
                     WHERE byte_length = excluded.byte_length",
                    catalog::main_table(&self.name)
                ),
                (cas.name(), hash.as_ref(), sqlite_length),
            )
            .context(RecordSnafu)?;
        if changed == 0 {
            return Err(ByteLengthReferenceError::ConflictingLength {
                cas_table: cas.name.clone(),
                hash,
            });
        }
        Ok(ByteLengthReference {
            cas_table: cas.name.clone(),
            hash,
            length,
        })
    }

    /// Loads and revalidates every cross-table fact.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid target meanings or geometry, absent or
    /// corrupt content, false lengths, malformed rows, or `SQLite` failures.
    pub fn facts(&self) -> Result<Vec<ByteLengthReference>, ByteLengthReferenceError> {
        validate_table(self.connection.neutron.sqlite(), &self.name)
    }
}

impl Connection {
    /// Discovers every interpreted cross-table byte-length relation.
    ///
    /// # Errors
    ///
    /// Returns an error when the catalog, relation, target CAS, or referenced
    /// content is invalid.
    pub fn byte_length_reference_tables(
        &self,
    ) -> Result<Vec<ByteLengthReferences<'_>>, ByteLengthReferenceError> {
        catalog::entries(self.neutron.sqlite())
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == INTERPRETATION)
            .map(|entry| {
                validate_table(self.neutron.sqlite(), &entry.table)?;
                Ok(wrapper(self, &entry.table))
            })
            .collect()
    }
}

pub(crate) fn create_table(sqlite: &sqlite::Connection, name: &str) -> sqlite::Result<()> {
    sqlite.execute_batch(&format!(
        "CREATE TABLE {} (
            cas_table TEXT NOT NULL,
            hash BLOB NOT NULL CHECK (length(hash) = 32),
            byte_length INTEGER NOT NULL CHECK (byte_length >= 0),
            PRIMARY KEY (cas_table, hash)
        ) STRICT, WITHOUT ROWID;",
        catalog::main_table(name)
    ))
}

pub(crate) fn wrapper<'conn>(
    connection: &'conn Connection,
    name: &str,
) -> ByteLengthReferences<'conn> {
    ByteLengthReferences {
        connection,
        name: name.to_owned(),
    }
}

pub(crate) fn validate_table(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<Vec<ByteLengthReference>, ByteLengthReferenceError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("cas_table"), String::from("TEXT"), true, 1),
            (String::from("hash"), String::from("BLOB"), true, 2),
            (
                String::from("byte_length"),
                String::from("INTEGER"),
                true,
                0,
            ),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(ByteLengthReferenceError::MalformedTable {
            table: name.to_owned(),
        });
    }

    let meanings = catalog::entries(sqlite)
        .map_err(map_catalog_error)?
        .into_iter()
        .map(|entry| (entry.table, entry.interpretation))
        .collect::<BTreeMap<_, _>>();
    let rows = load_rows(sqlite, name)?;
    let mut validated_targets = BTreeSet::new();
    let mut facts = Vec::with_capacity(rows.len());
    for (cas_name, hash, length) in rows {
        let hash = <[u8; 32]>::try_from(hash)
            .map(O256::from_array)
            .map_err(|_| ByteLengthReferenceError::MalformedHash {
                table: name.to_owned(),
            })?;
        let length =
            u64::try_from(length).map_err(|_| ByteLengthReferenceError::NegativeLength {
                table: name.to_owned(),
            })?;
        if validated_targets.insert(cas_name.clone()) {
            if meanings.get(&cas_name).map(String::as_str) != Some(cas_table::INTERPRETATION) {
                return Err(ByteLengthReferenceError::WrongTargetMeaning {
                    relation: name.to_owned(),
                    cas_table: cas_name,
                });
            }
            cas_table::validate_table(sqlite, &cas_name).context(CasSnafu)?;
        }
        let data = cas_table::fetch(sqlite, &cas_name, hash)
            .context(CasSnafu)?
            .ok_or_else(|| ByteLengthReferenceError::MissingObject {
                relation: name.to_owned(),
                cas_table: cas_name.clone(),
                hash,
            })?;
        let actual =
            u64::try_from(data.len()).map_err(|_| ByteLengthReferenceError::LengthOutOfRange)?;
        if actual != length {
            return Err(ByteLengthReferenceError::False {
                relation: name.to_owned(),
                cas_table: cas_name,
                hash,
                claimed: length,
                actual,
            });
        }
        facts.push(ByteLengthReference {
            cas_table: cas_name,
            hash,
            length,
        });
    }
    Ok(facts)
}

type RawRow = (String, Vec<u8>, i64);

fn load_rows(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<Vec<RawRow>, ByteLengthReferenceError> {
    sqlite
        .prepare(&format!(
            "SELECT cas_table, hash, byte_length FROM {} ORDER BY cas_table, hash",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)
}

fn map_catalog_error(error: crate::CatalogError) -> ByteLengthReferenceError {
    match error {
        crate::CatalogError::Sqlite { source } => ByteLengthReferenceError::Catalog { source },
        source => ByteLengthReferenceError::InvalidCatalog { source },
    }
}

/// Failure to construct, validate, or use a cross-table length relation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ByteLengthReferenceError {
    /// Wrappers from different Nucleus connections were combined.
    #[snafu(display("cross-table relationship wrappers belong to different connections"))]
    DifferentConnection,

    /// A byte length cannot be represented by this implementation.
    #[snafu(display("byte length is outside the supported range"))]
    LengthOutOfRange,

    /// The persistent catalog is logically invalid.
    #[snafu(display("{source}"))]
    InvalidCatalog {
        /// Underlying catalog failure.
        source: crate::CatalogError,
    },

    /// The persistent catalog could not be read.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// The relation has the wrong representation.
    #[snafu(display("byte-length reference table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// A row contains a malformed address.
    #[snafu(display("byte-length reference table {table:?} contains a malformed address"))]
    MalformedHash {
        /// Physical table.
        table: String,
    },

    /// A row contains a negative length.
    #[snafu(display("byte-length reference table {table:?} contains a negative length"))]
    NegativeLength {
        /// Physical table.
        table: String,
    },

    /// A target is absent or does not have CAS meaning.
    #[snafu(display("byte-length relation {relation:?} references non-CAS table {cas_table:?}"))]
    WrongTargetMeaning {
        /// Source relation.
        relation: String,
        /// Rejected target.
        cas_table: String,
    },

    /// The target CAS does not contain resident bytes for the address.
    #[snafu(display(
        "byte-length relation {relation:?} references absent content {hash} in {cas_table:?}"
    ))]
    MissingObject {
        /// Source relation.
        relation: String,
        /// Target CAS.
        cas_table: String,
        /// Missing address.
        hash: O256,
    },

    /// A claimed length differs from the resident bytes.
    #[snafu(display(
        "byte-length relation {relation:?} claims {cas_table:?}/{hash} has length {claimed}, actual length is {actual}"
    ))]
    False {
        /// Source relation.
        relation: String,
        /// Target CAS.
        cas_table: String,
        /// Stable address.
        hash: O256,
        /// Claimed length.
        claimed: u64,
        /// Actual length.
        actual: u64,
    },

    /// An existing row claims a different length for the same target.
    #[snafu(display("conflicting length claim for {cas_table:?}/{hash}"))]
    ConflictingLength {
        /// Target CAS.
        cas_table: String,
        /// Stable address.
        hash: O256,
    },

    /// The relation could not be scanned.
    #[snafu(display("could not scan byte-length references: {source}"))]
    Scan {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// A fact could not be recorded.
    #[snafu(display("could not record byte-length reference: {source}"))]
    Record {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// A target CAS operation failed.
    #[snafu(display("could not validate referenced CAS content: {source}"))]
    Cas {
        /// Underlying failure.
        source: crate::CasTableError,
    },
}
