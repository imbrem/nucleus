use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{self as sqlite, OptionalExtension};

use crate::{Connection, catalog};

pub(crate) const INTERPRETATION: &str = "cov.cas.indexed/v0";

/// A table-local integer identity for one persistent CAS entry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasObjectId(i64);

impl CasObjectId {
    /// Returns the underlying table-local integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// A validated persistent indexed content-addressed store.
///
/// Every row assigns a table-local integer to a stable [`O256`]. Resident
/// bytes are optional, allowing an address to be declared before its content
/// is available.
#[derive(Debug)]
pub struct CasTable<'conn> {
    pub(crate) connection: &'conn Connection,
    pub(crate) name: String,
}

impl CasTable<'_> {
    /// Returns the physical child table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Computes the stable content address of ordinary bytes.
    #[must_use]
    pub fn hash(&self, data: &[u8]) -> O256 {
        O256::from_bytes(data)
    }

    /// Stores bytes and returns their stable address.
    ///
    /// # Errors
    ///
    /// Returns an error for conflicting resident bytes or `SQLite` failures.
    pub fn store(&self, data: &[u8]) -> Result<O256, CasTableError> {
        let hash = self.hash(data);
        self.intern_with_hash(hash, data)?;
        Ok(hash)
    }

    /// Stores bytes and returns their table-local identity.
    ///
    /// # Errors
    ///
    /// Returns an error for conflicting resident bytes or `SQLite` failures.
    pub fn intern(&self, data: &[u8]) -> Result<CasObjectId, CasTableError> {
        let hash = self.hash(data);
        self.intern_with_hash(hash, data)
    }

    fn intern_with_hash(&self, hash: O256, data: &[u8]) -> Result<CasObjectId, CasTableError> {
        self.connection
            .neutron
            .sqlite()
            .query_row(
                &format!(
                    "INSERT INTO {} (hash, data) VALUES (?1, ?2)
                     ON CONFLICT (hash) DO UPDATE SET data = excluded.data
                     WHERE data IS NULL OR data = excluded.data
                     RETURNING object_id",
                    catalog::main_table(&self.name)
                ),
                (hash.as_ref(), data),
                |row| row.get::<_, i64>(0).map(CasObjectId),
            )
            .optional()
            .context(StoreSnafu)?
            .ok_or(CasTableError::HashCollision { hash })
    }

    /// Returns the existing ID for `hash`, or declares an unresolved entry.
    ///
    /// # Errors
    ///
    /// Returns an error when the table cannot be updated or queried.
    pub fn declare(&self, hash: O256) -> Result<CasObjectId, CasTableError> {
        self.connection
            .neutron
            .sqlite()
            .execute(
                &format!(
                    "INSERT INTO {} (hash, data) VALUES (?1, NULL)
                     ON CONFLICT (hash) DO NOTHING",
                    catalog::main_table(&self.name)
                ),
                [hash.as_ref()],
            )
            .context(DeclareSnafu)?;
        self.resolve(hash)?
            .ok_or(CasTableError::DeclaredAddressMissing { hash })
    }

    /// Resolves a stable address to a table-local identity.
    ///
    /// # Errors
    ///
    /// Returns an error when the table cannot be queried.
    pub fn resolve(&self, hash: O256) -> Result<Option<CasObjectId>, CasTableError> {
        self.connection
            .neutron
            .sqlite()
            .query_row(
                &format!(
                    "SELECT object_id FROM {} WHERE hash = ?1",
                    catalog::main_table(&self.name)
                ),
                [hash.as_ref()],
                |row| row.get::<_, i64>(0).map(CasObjectId),
            )
            .optional()
            .context(ResolveSnafu)
    }

    /// Returns the stable address assigned to a table-local identity.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed addresses or `SQLite` failures.
    pub fn address(&self, id: CasObjectId) -> Result<Option<O256>, CasTableError> {
        let bytes = self
            .connection
            .neutron
            .sqlite()
            .query_row(
                &format!(
                    "SELECT hash FROM {} WHERE object_id = ?1",
                    catalog::main_table(&self.name)
                ),
                [id.0],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()
            .context(AddressSnafu)?;
        bytes
            .map(|bytes| decode_address(&self.name, bytes))
            .transpose()
    }

    /// Fetches resident bytes by stable address.
    ///
    /// # Errors
    ///
    /// Returns an error when the table cannot be queried.
    pub fn fetch(&self, hash: O256) -> Result<Option<Vec<u8>>, CasTableError> {
        fetch(self.connection.neutron.sqlite(), &self.name, hash)
    }

    /// Fetches resident bytes by table-local identity.
    ///
    /// # Errors
    ///
    /// Returns an error when the table cannot be queried.
    pub fn fetch_id(&self, id: CasObjectId) -> Result<Option<Vec<u8>>, CasTableError> {
        self.connection
            .neutron
            .sqlite()
            .query_row(
                &format!(
                    "SELECT data FROM {} WHERE object_id = ?1",
                    catalog::main_table(&self.name)
                ),
                [id.0],
                |row| row.get::<_, Option<Vec<u8>>>(0),
            )
            .optional()
            .context(FetchSnafu)
            .map(Option::flatten)
    }

    /// Fills an existing entry with matching ordinary content bytes.
    ///
    /// Returns `true` if bytes were already resident.
    ///
    /// # Errors
    ///
    /// Returns an error when the ID is absent, the address does not match, or
    /// the table cannot be updated.
    pub fn fill(&self, id: CasObjectId, data: &[u8]) -> Result<bool, CasTableError> {
        let (hash, resident) = self
            .connection
            .neutron
            .sqlite()
            .query_row(
                &format!(
                    "SELECT hash, data IS NOT NULL FROM {} WHERE object_id = ?1",
                    catalog::main_table(&self.name)
                ),
                [id.0],
                |row| Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, bool>(1)?)),
            )
            .optional()
            .context(FillSnafu)?
            .ok_or(CasTableError::MissingId { id })?;
        let expected = decode_address(&self.name, hash)?;
        let actual = self.hash(data);
        if actual != expected {
            return Err(CasTableError::AddressMismatch {
                table: self.name.clone(),
                expected,
                actual,
            });
        }
        self.connection
            .neutron
            .sqlite()
            .execute(
                &format!(
                    "UPDATE {} SET data = ?2 WHERE object_id = ?1",
                    catalog::main_table(&self.name)
                ),
                (id.0, data),
            )
            .context(FillSnafu)?;
        Ok(resident)
    }

    /// Evicts resident bytes while preserving ID and stable address.
    ///
    /// # Errors
    ///
    /// Returns an error when the table cannot be updated.
    pub fn evict(&self, id: CasObjectId) -> Result<bool, CasTableError> {
        self.connection
            .neutron
            .sqlite()
            .execute(
                &format!(
                    "UPDATE {} SET data = NULL
                     WHERE object_id = ?1 AND data IS NOT NULL",
                    catalog::main_table(&self.name)
                ),
                [id.0],
            )
            .context(EvictSnafu)
            .map(|changed| changed != 0)
    }
}

impl Connection {
    /// Discovers and validates every interpreted persistent CAS table.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed catalogs, incompatible tables, corrupt
    /// resident content, or `SQLite` failures.
    pub fn cas_tables(&self) -> Result<Vec<CasTable<'_>>, CasTableError> {
        crate::catalog::entries(self.neutron.sqlite())
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
            object_id INTEGER PRIMARY KEY,
            hash BLOB NOT NULL UNIQUE CHECK (length(hash) = 32),
            data BLOB
        ) STRICT;",
        catalog::main_table(name)
    ))
}

pub(crate) fn wrapper<'conn>(connection: &'conn Connection, name: &str) -> CasTable<'conn> {
    CasTable {
        connection,
        name: name.to_owned(),
    }
}

pub(crate) fn fetch(
    sqlite: &sqlite::Connection,
    name: &str,
    hash: O256,
) -> Result<Option<Vec<u8>>, CasTableError> {
    sqlite
        .query_row(
            &format!(
                "SELECT data FROM {} WHERE hash = ?1",
                catalog::main_table(name)
            ),
            [hash.as_ref()],
            |row| row.get::<_, Option<Vec<u8>>>(0),
        )
        .optional()
        .context(FetchSnafu)
        .map(Option::flatten)
}

pub(crate) fn validate_table(sqlite: &sqlite::Connection, name: &str) -> Result<(), CasTableError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("object_id"), String::from("INTEGER"), false, 1),
            (String::from("hash"), String::from("BLOB"), true, 0),
            (String::from("data"), String::from("BLOB"), false, 0),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, false)
        || catalog::unique_indexes(sqlite, name).context(ScanSnafu)? != [vec![String::from("hash")]]
    {
        return Err(CasTableError::MalformedTable {
            table: name.to_owned(),
        });
    }

    let rows = sqlite
        .prepare(&format!(
            "SELECT hash, data FROM {} ORDER BY object_id",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, Option<Vec<u8>>>(1)?))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    for (hash, data) in rows {
        let expected = decode_address(name, hash)?;
        if let Some(data) = data {
            let actual = O256::from_bytes(&data);
            if actual != expected {
                return Err(CasTableError::AddressMismatch {
                    table: name.to_owned(),
                    expected,
                    actual,
                });
            }
        }
    }
    Ok(())
}

fn decode_address(table: &str, bytes: Vec<u8>) -> Result<O256, CasTableError> {
    <[u8; 32]>::try_from(bytes)
        .map(O256::from_array)
        .map_err(|_| CasTableError::MalformedHash {
            table: table.to_owned(),
        })
}

fn map_catalog_error(error: crate::CatalogError) -> CasTableError {
    match error {
        crate::CatalogError::Sqlite { source } => CasTableError::Catalog { source },
        source => CasTableError::InvalidCatalog { source },
    }
}

/// Failure to construct, validate, or use a persistent indexed CAS.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasTableError {
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

    /// A persistent CAS has the wrong physical representation.
    #[snafu(display("CAS table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// A stored address is not 32 bytes.
    #[snafu(display("CAS table {table:?} contains a malformed content address"))]
    MalformedHash {
        /// Physical table.
        table: String,
    },

    /// Resident bytes do not match their stable address.
    #[snafu(display(
        "CAS table {table:?} stores content addressed as {expected}, actual address is {actual}"
    ))]
    AddressMismatch {
        /// Physical table.
        table: String,
        /// Recorded address.
        expected: O256,
        /// Computed address.
        actual: O256,
    },

    /// Distinct resident bytes collided at one address.
    #[snafu(display("hash collision at content address {hash}"))]
    HashCollision {
        /// Conflicting address.
        hash: O256,
    },

    /// A table-local identity does not exist.
    #[snafu(display("CAS object ID {} does not exist", id.get()))]
    MissingId {
        /// Missing identity.
        id: CasObjectId,
    },

    /// A declaration was inserted but could not be resolved.
    #[snafu(display("declared content address {hash} could not be resolved"))]
    DeclaredAddressMissing {
        /// Declared address.
        hash: O256,
    },

    /// Bytes could not be stored.
    #[snafu(display("could not store persistent CAS bytes: {source}"))]
    Store {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An unresolved address could not be declared.
    #[snafu(display("could not declare persistent CAS address: {source}"))]
    Declare {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An address could not be resolved.
    #[snafu(display("could not resolve persistent CAS address: {source}"))]
    Resolve {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An address could not be read by local ID.
    #[snafu(display("could not read persistent CAS address: {source}"))]
    Address {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// Resident bytes could not be fetched.
    #[snafu(display("could not fetch persistent CAS bytes: {source}"))]
    Fetch {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// An existing entry could not be filled.
    #[snafu(display("could not fill persistent CAS entry: {source}"))]
    Fill {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// Resident bytes could not be evicted.
    #[snafu(display("could not evict persistent CAS bytes: {source}"))]
    Evict {
        /// Underlying failure.
        source: sqlite::Error,
    },

    /// The persistent CAS could not be validated.
    #[snafu(display("could not scan persistent CAS: {source}"))]
    Scan {
        /// Underlying failure.
        source: sqlite::Error,
    },
}
