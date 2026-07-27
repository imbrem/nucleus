use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{self as sqlite, OptionalExtension};

use crate::{Connection, catalog};

pub(crate) const INTERPRETATION: &str = "cov.cas/v0";

/// A validated persistent content-addressed table.
///
/// Stable content hashes are the only logical identities in this
/// representation. Unlike the connection-local default CAS, this initial
/// persistent form has no local integer index and no unresolved entries.
#[derive(Debug)]
pub struct CasTable<'conn> {
    sqlite: &'conn sqlite::Connection,
    name: String,
}

impl CasTable<'_> {
    /// Returns the physical table name recorded in the persistent catalog.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Computes the stable address of `data`.
    #[must_use]
    pub fn hash(&self, data: &[u8]) -> O256 {
        O256::from_bytes(data)
    }

    /// Stores `data` and returns its stable address.
    ///
    /// # Errors
    ///
    /// Returns an error if existing bytes at the computed address differ or
    /// the table cannot be updated.
    pub fn store(&self, data: &[u8]) -> Result<O256, CasTableError> {
        let hash = self.hash(data);
        let changed = self
            .sqlite
            .execute(
                &format!(
                    "INSERT INTO {} (hash, data) VALUES (?1, ?2)
                     ON CONFLICT (hash) DO UPDATE SET data = excluded.data
                     WHERE data = excluded.data",
                    catalog::quote_identifier(&self.name)
                ),
                (hash.as_ref(), data),
            )
            .context(StoreSnafu)?;
        if changed == 0 {
            return Err(CasTableError::HashCollision { hash });
        }
        Ok(hash)
    }

    /// Fetches bytes by stable address.
    ///
    /// # Errors
    ///
    /// Returns an error if the table cannot be queried.
    pub fn fetch(&self, hash: O256) -> Result<Option<Vec<u8>>, CasTableError> {
        self.sqlite
            .query_row(
                &format!(
                    "SELECT data FROM {} WHERE hash = ?1",
                    catalog::quote_identifier(&self.name)
                ),
                [hash.as_ref()],
                |row| row.get(0),
            )
            .optional()
            .context(FetchSnafu)
    }
}

impl Connection {
    /// Creates, catalogs, and returns a canonical persistent CAS table.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested transactions,
    /// or `SQLite` failures.
    pub fn create_cas_table(&self, name: &str) -> Result<CasTable<'_>, CasTableError> {
        if catalog::name_is_reserved(name) {
            return Err(CasTableError::ReservedName {
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
                    hash BLOB NOT NULL PRIMARY KEY CHECK (length(hash) = 32),
                    data BLOB NOT NULL
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
        Ok(CasTable {
            sqlite: self.neutron.sqlite(),
            name: name.to_owned(),
        })
    }

    /// Discovers and validates every persistent CAS table.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed catalog, incompatible table, corrupt
    /// content address, or `SQLite` failure.
    pub fn cas_tables(&self) -> Result<Vec<CasTable<'_>>, CasTableError> {
        let sqlite = self.neutron.sqlite();
        catalog::entries(sqlite)
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == INTERPRETATION)
            .map(|entry| {
                validate_table(sqlite, &entry.table)?;
                Ok(CasTable {
                    sqlite,
                    name: entry.table,
                })
            })
            .collect()
    }
}

pub(crate) fn validate_table(sqlite: &sqlite::Connection, name: &str) -> Result<(), CasTableError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("hash"), String::from("BLOB"), true, 1),
            (String::from("data"), String::from("BLOB"), true, 0),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(CasTableError::MalformedTable {
            table: name.to_owned(),
        });
    }

    let mut statement = sqlite
        .prepare(&format!(
            "SELECT hash, data FROM {} ORDER BY hash",
            catalog::quote_identifier(name)
        ))
        .context(ScanSnafu)?;
    let rows = statement
        .query_map((), |row| {
            Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, Vec<u8>>(1)?))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    for (hash, data) in rows {
        let expected = <[u8; 32]>::try_from(hash)
            .map(O256::from_array)
            .map_err(|_| CasTableError::MalformedHash {
                table: name.to_owned(),
            })?;
        let actual = O256::from_bytes(&data);
        if actual != expected {
            return Err(CasTableError::AddressMismatch {
                table: name.to_owned(),
                expected,
                actual,
            });
        }
    }
    Ok(())
}

fn map_catalog_error(error: crate::CatalogError) -> CasTableError {
    match error {
        crate::CatalogError::Malformed => CasTableError::MalformedCatalog,
        crate::CatalogError::Sqlite { source } => CasTableError::Catalog { source },
    }
}

/// Failure to construct, discover, or use a persistent CAS table.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasTableError {
    /// The requested table name belongs to Nucleus or `SQLite`.
    #[snafu(display("CAS table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected name.
        name: String,
    },

    /// The persistent catalog is malformed.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    MalformedCatalog,

    /// A catalogued CAS table has the wrong representation.
    #[snafu(display("CAS table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// A stored hash does not contain exactly 32 bytes.
    #[snafu(display("CAS table {table:?} contains a malformed content address"))]
    MalformedHash {
        /// Physical table.
        table: String,
    },

    /// Resident data does not match its stable address.
    #[snafu(display(
        "CAS table {table:?} stores bytes with address {actual} at expected address {expected}"
    ))]
    AddressMismatch {
        /// Physical table.
        table: String,
        /// Address recorded by the table.
        expected: O256,
        /// Address computed from resident bytes.
        actual: O256,
    },

    /// Different resident bytes have the same computed address.
    #[snafu(display("hash collision at content address {hash}"))]
    HashCollision {
        /// Conflicting stable address.
        hash: O256,
    },

    /// The catalog could not be inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The table could not be created.
    #[snafu(display("could not create persistent CAS table: {source}"))]
    Create {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The table could not be validated.
    #[snafu(display("could not scan persistent CAS table: {source}"))]
    Scan {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// Bytes could not be stored.
    #[snafu(display("could not store bytes in persistent CAS table: {source}"))]
    Store {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// Bytes could not be fetched.
    #[snafu(display("could not fetch bytes from persistent CAS table: {source}"))]
    Fetch {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}
