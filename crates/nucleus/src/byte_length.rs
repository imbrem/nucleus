use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Connection, catalog};

pub(crate) const INTERPRETATION: &str = "cov.bytes.length/v0";

/// A checked statement that a byte vector has a particular length.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteLengthFact {
    bytes: Vec<u8>,
    length: u64,
}

impl ByteLengthFact {
    /// Checks and constructs a byte-length fact.
    ///
    /// # Errors
    ///
    /// Returns an error when `length` is not the length of `bytes`.
    pub fn new(bytes: impl Into<Vec<u8>>, length: u64) -> Result<Self, ByteLengthError> {
        let bytes = bytes.into();
        let actual = u64::try_from(bytes.len()).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        if actual != length {
            return Err(ByteLengthError::False {
                claimed: length,
                actual,
            });
        }
        Ok(Self { bytes, length })
    }

    /// Measures and constructs a byte-length fact.
    ///
    /// # Errors
    ///
    /// Returns an error only on platforms whose `usize` does not fit in
    /// `u64`.
    pub fn measure(bytes: impl Into<Vec<u8>>) -> Result<Self, ByteLengthError> {
        let bytes = bytes.into();
        let length = u64::try_from(bytes.len()).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        Ok(Self { bytes, length })
    }

    /// Returns the byte vector.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the checked byte length.
    #[must_use]
    pub const fn length(&self) -> u64 {
        self.length
    }
}

/// A validated byte-length relation in a Nucleus connection.
#[derive(Debug)]
pub struct ByteLengths<'conn> {
    sqlite: &'conn sqlite::Connection,
    name: String,
}

impl ByteLengths<'_> {
    /// Returns the physical table name recorded in the catalog.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Inserts one checked fact.
    ///
    /// # Errors
    ///
    /// Returns an error when the length does not fit in an `SQLite` integer
    /// or the insertion fails.
    pub fn insert(&self, fact: ByteLengthFact) -> Result<(), ByteLengthError> {
        let length = i64::try_from(fact.length).map_err(|_| ByteLengthError::LengthOutOfRange)?;
        self.sqlite
            .execute(
                &format!(
                    "INSERT INTO {} (bytes, byte_length) VALUES (?1, ?2)",
                    catalog::main_table(&self.name)
                ),
                (fact.bytes, length),
            )
            .context(InsertSnafu)?;
        Ok(())
    }

    /// Loads and checks every fact in the relation.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or false rows and `SQLite` failures.
    pub fn facts(&self) -> Result<Vec<ByteLengthFact>, ByteLengthError> {
        load_facts(self.sqlite, &self.name)
    }
}

impl Connection {
    /// Creates, catalogs, and returns a canonical byte-length relation.
    ///
    /// This first representation stores the bytes directly. It deliberately
    /// introduces no table ownership or cross-table references.
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
        let transaction = self
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateSnafu)?;
        create_table(&transaction, name).context(CreateSnafu)?;
        transaction
            .execute(
                "INSERT INTO main.cov_catalog (table_name, interpretation) VALUES (?1, ?2)",
                (name, INTERPRETATION),
            )
            .context(CreateSnafu)?;
        transaction.commit().context(CreateSnafu)?;
        Ok(wrapper(self.neutron.sqlite(), name))
    }

    /// Discovers and validates every directly catalogued byte-length relation.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed catalogs, incompatible tables, false
    /// rows, or `SQLite` failures.
    pub fn byte_length_tables(&self) -> Result<Vec<ByteLengths<'_>>, ByteLengthError> {
        let sqlite = self.neutron.sqlite();
        catalog::entries(sqlite)
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == INTERPRETATION)
            .map(|entry| {
                validate_table(sqlite, &entry.table)?;
                Ok(ByteLengths {
                    sqlite,
                    name: entry.table,
                })
            })
            .collect()
    }
}

pub(crate) fn create_table(sqlite: &sqlite::Connection, name: &str) -> sqlite::Result<()> {
    let quoted = catalog::main_table(name);
    sqlite.execute_batch(&format!(
        "CREATE TABLE {quoted} (
            bytes BLOB NOT NULL PRIMARY KEY,
            byte_length INTEGER NOT NULL
                CHECK (byte_length >= 0 AND byte_length = length(bytes))
        ) STRICT, WITHOUT ROWID;"
    ))
}

pub(crate) fn wrapper<'conn>(sqlite: &'conn sqlite::Connection, name: &str) -> ByteLengths<'conn> {
    ByteLengths {
        sqlite,
        name: name.to_owned(),
    }
}

pub(crate) fn validate_table(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<(), ByteLengthError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("bytes"), String::from("BLOB"), true, 1),
            (
                String::from("byte_length"),
                String::from("INTEGER"),
                true,
                0,
            ),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(ByteLengthError::MalformedTable {
            table: name.to_owned(),
        });
    }
    load_facts(sqlite, name)?;
    Ok(())
}

fn load_facts(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<Vec<ByteLengthFact>, ByteLengthError> {
    let rows = sqlite
        .prepare(&format!(
            "SELECT bytes, byte_length FROM {} ORDER BY bytes",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, i64>(1)?))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    rows.into_iter()
        .map(|(bytes, length)| {
            let length = u64::try_from(length).map_err(|_| ByteLengthError::NegativeLength {
                table: name.to_owned(),
            })?;
            ByteLengthFact::new(bytes, length)
        })
        .collect()
}

fn map_catalog_error(error: catalog::CatalogError) -> ByteLengthError {
    match error {
        catalog::CatalogError::Sqlite { source } => ByteLengthError::Catalog { source },
        _ => ByteLengthError::MalformedCatalog,
    }
}

/// Failure to construct, discover, or use a byte-length relation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ByteLengthError {
    /// A proposed fact is false.
    #[snafu(display("claimed byte length {claimed}, actual length is {actual}"))]
    False {
        /// Claimed length.
        claimed: u64,
        /// Actual length.
        actual: u64,
    },

    /// A byte length cannot be represented by this implementation.
    #[snafu(display("byte length is outside the supported range"))]
    LengthOutOfRange,

    /// The requested table name belongs to Nucleus or `SQLite`.
    #[snafu(display("byte-length table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected name.
        name: String,
    },

    /// The persistent catalog is malformed.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    MalformedCatalog,

    /// A catalogued byte-length relation has the wrong representation.
    #[snafu(display("byte-length table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// A row contains a negative byte length.
    #[snafu(display("byte-length table {table:?} contains a negative length"))]
    NegativeLength {
        /// Physical table.
        table: String,
    },

    /// The persistent catalog could not be inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The relation could not be created.
    #[snafu(display("could not create byte-length table: {source}"))]
    Create {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The relation could not be scanned.
    #[snafu(display("could not scan byte-length table: {source}"))]
    Scan {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// A fact could not be inserted.
    #[snafu(display("could not insert byte-length fact: {source}"))]
    Insert {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}
