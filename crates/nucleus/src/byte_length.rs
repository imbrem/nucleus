use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use crate::{CasTable, Connection, cas_table, catalog};

pub(crate) const INTERPRETATION: &str = "cov.bytes.length/v0";

/// One checked statement about the length of a content-addressed byte vector.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteLengthFact {
    /// Persistent CAS table containing the bytes.
    pub cas_table: String,
    /// Stable address of the bytes.
    pub hash: O256,
    /// Number of bytes in the vector.
    pub length: u64,
}

/// A validated relation from persistent CAS locations to byte lengths.
///
/// Each row identifies its target as `(cas_table, hash)`, allowing one
/// relation to refer to several independently catalogued CAS tables.
#[derive(Debug)]
pub struct ByteLengths<'conn> {
    connection: &'conn Connection,
    name: String,
}

impl ByteLengths<'_> {
    /// Returns the physical table name recorded in the persistent catalog.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Stores `data` in `cas` and records its checked length.
    ///
    /// # Errors
    ///
    /// Returns an error if the wrappers belong to different connections, the
    /// vector is too large for `SQLite`, or either table cannot be updated.
    pub fn record(
        &self,
        cas: &CasTable<'_>,
        data: &[u8],
    ) -> Result<ByteLengthFact, ByteLengthError> {
        if !std::ptr::eq(cas.sqlite, self.connection.neutron.sqlite()) {
            return Err(ByteLengthError::DifferentConnection);
        }
        let length_u64 =
            u64::try_from(data.len()).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        let length = i64::try_from(length_u64).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        let hash = cas.store(data).context(CasSnafu)?;
        let changed = self
            .connection
            .neutron
            .sqlite()
            .execute(
                &format!(
                    "INSERT INTO {} (cas_table, hash, length) VALUES (?1, ?2, ?3)
                     ON CONFLICT (cas_table, hash) DO UPDATE SET length = excluded.length
                     WHERE length = excluded.length",
                    catalog::quote_identifier(&self.name)
                ),
                (cas.name(), hash.as_ref(), length),
            )
            .context(RecordSnafu)?;
        if changed == 0 {
            return Err(ByteLengthError::ConflictingLength {
                cas_table: cas.name.clone(),
                hash,
            });
        }
        Ok(ByteLengthFact {
            cas_table: cas.name.clone(),
            hash,
            length: length_u64,
        })
    }

    /// Loads and revalidates every length fact.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed rows, missing or invalid target CAS
    /// tables, absent bytes, incorrect lengths, or `SQLite` failures.
    pub fn facts(&self) -> Result<Vec<ByteLengthFact>, ByteLengthError> {
        validate_table(self.connection.neutron.sqlite(), &self.name)
    }
}

impl Connection {
    /// Creates, catalogs, and returns a byte-length relation.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested transactions,
    /// or `SQLite` failures.
    pub fn create_byte_lengths(&self, name: &str) -> Result<ByteLengths<'_>, ByteLengthError> {
        if catalog::name_is_reserved(name) {
            return Err(ByteLengthError::ReservedName {
                name: name.to_owned(),
            });
        }
        let quoted = catalog::quote_identifier(name);
        let transaction = self
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateSnafu)?;
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {quoted} (
                    cas_table TEXT NOT NULL,
                    hash BLOB NOT NULL CHECK (length(hash) = 32),
                    length INTEGER NOT NULL CHECK (length >= 0),
                    PRIMARY KEY (cas_table, hash)
                ) STRICT, WITHOUT ROWID;"
            ))
            .context(CreateSnafu)?;
        transaction
            .execute(
                "INSERT INTO cov_catalog (table_name, interpretation) VALUES (?1, ?2)",
                (name, INTERPRETATION),
            )
            .context(CreateSnafu)?;
        transaction.commit().context(CreateSnafu)?;
        Ok(ByteLengths {
            connection: self,
            name: name.to_owned(),
        })
    }

    /// Discovers and validates every byte-length relation.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed catalog, relation, target CAS, or
    /// referenced fact.
    pub fn byte_length_tables(&self) -> Result<Vec<ByteLengths<'_>>, ByteLengthError> {
        catalog::entries(self.neutron.sqlite())
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == INTERPRETATION)
            .map(|entry| {
                validate_table(self.neutron.sqlite(), &entry.table)?;
                Ok(ByteLengths {
                    connection: self,
                    name: entry.table,
                })
            })
            .collect()
    }
}

pub(crate) fn validate_table(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<Vec<ByteLengthFact>, ByteLengthError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("cas_table"), String::from("TEXT"), true, 1),
            (String::from("hash"), String::from("BLOB"), true, 2),
            (String::from("length"), String::from("INTEGER"), true, 0),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(ByteLengthError::MalformedTable {
            table: name.to_owned(),
        });
    }

    let catalog = catalog::entries(sqlite)
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
            .map_err(|_| ByteLengthError::MalformedHash {
                table: name.to_owned(),
            })?;
        let length = u64::try_from(length).map_err(|_| ByteLengthError::NegativeLength {
            table: name.to_owned(),
        })?;
        if validated_targets.insert(cas_name.clone()) {
            if catalog.get(&cas_name).map(String::as_str) != Some(cas_table::INTERPRETATION) {
                return Err(ByteLengthError::MissingCas {
                    relation: name.to_owned(),
                    cas_table: cas_name,
                });
            }
            cas_table::validate_table(sqlite, &cas_name).context(CasSnafu)?;
        }
        let data = cas_table::fetch(sqlite, &cas_name, hash)
            .context(CasSnafu)?
            .ok_or_else(|| ByteLengthError::MissingObject {
                relation: name.to_owned(),
                cas_table: cas_name.clone(),
                hash,
            })?;
        let actual = u64::try_from(data.len()).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        if actual != length {
            return Err(ByteLengthError::WrongLength {
                relation: name.to_owned(),
                cas_table: cas_name,
                hash,
                expected: length,
                actual,
            });
        }
        facts.push(ByteLengthFact {
            cas_table: cas_name,
            hash,
            length,
        });
    }
    Ok(facts)
}

type RawRow = (String, Vec<u8>, i64);

fn load_rows(sqlite: &sqlite::Connection, name: &str) -> Result<Vec<RawRow>, ByteLengthError> {
    sqlite
        .prepare(&format!(
            "SELECT cas_table, hash, length FROM {} ORDER BY cas_table, hash",
            catalog::quote_identifier(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)
}

fn map_catalog_error(error: crate::CatalogError) -> ByteLengthError {
    match error {
        crate::CatalogError::Malformed => ByteLengthError::MalformedCatalog,
        crate::CatalogError::Sqlite { source } => ByteLengthError::Catalog { source },
    }
}

/// Failure to construct, discover, or validate a byte-length relation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ByteLengthError {
    /// The requested table name belongs to Nucleus or `SQLite`.
    #[snafu(display("byte-length table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected name.
        name: String,
    },

    /// The persistent catalog is malformed.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    MalformedCatalog,

    /// A catalogued byte-length table has the wrong representation.
    #[snafu(display("byte-length table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// A row contains a malformed stable address.
    #[snafu(display("byte-length table {table:?} contains a malformed content address"))]
    MalformedHash {
        /// Physical relation.
        table: String,
    },

    /// A row contains a negative byte length.
    #[snafu(display("byte-length table {table:?} contains a negative length"))]
    NegativeLength {
        /// Physical relation.
        table: String,
    },

    /// A referenced table is absent or is not a persistent CAS.
    #[snafu(display(
        "byte-length relation {relation:?} references missing CAS table {cas_table:?}"
    ))]
    MissingCas {
        /// Physical source relation.
        relation: String,
        /// Referenced target table.
        cas_table: String,
    },

    /// A referenced CAS does not contain the named bytes.
    #[snafu(display(
        "byte-length relation {relation:?} references absent object {hash} in {cas_table:?}"
    ))]
    MissingObject {
        /// Physical source relation.
        relation: String,
        /// Referenced target CAS.
        cas_table: String,
        /// Missing stable address.
        hash: O256,
    },

    /// A row's claimed length differs from the resident byte vector.
    #[snafu(display(
        "byte-length relation {relation:?} claims {cas_table:?}/{hash} has length {expected}, actual length is {actual}"
    ))]
    WrongLength {
        /// Physical source relation.
        relation: String,
        /// Referenced target CAS.
        cas_table: String,
        /// Stable address of the bytes.
        hash: O256,
        /// Claimed length.
        expected: u64,
        /// Checked length.
        actual: u64,
    },

    /// A row already claims a different length for the same target.
    #[snafu(display(
        "byte-length relation already contains a conflicting claim for {cas_table:?}/{hash}"
    ))]
    ConflictingLength {
        /// Referenced target CAS.
        cas_table: String,
        /// Stable address of the bytes.
        hash: O256,
    },

    /// Wrappers from different connections were combined.
    #[snafu(display("cross-table relationship wrappers belong to different connections"))]
    DifferentConnection,

    /// A byte vector is too large for `SQLite`'s signed integer representation.
    #[snafu(display("byte vector length does not fit in a SQLite INTEGER"))]
    LengthOutOfRange,

    /// The persistent catalog could not be inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The relationship table could not be created.
    #[snafu(display("could not create byte-length relation: {source}"))]
    Create {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The relationship table could not be scanned.
    #[snafu(display("could not scan byte-length relation: {source}"))]
    Scan {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// A relationship row could not be recorded.
    #[snafu(display("could not record byte-length fact: {source}"))]
    Record {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// A target persistent CAS operation failed.
    #[snafu(display("could not validate referenced CAS content: {source}"))]
    Cas {
        /// Underlying failure.
        source: crate::CasTableError,
    },
}
