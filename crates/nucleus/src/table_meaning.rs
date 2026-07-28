use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Addition, ByteLengths, Connection, addition, byte_length, catalog};

pub(crate) const INTERPRETATION: &str = "cov.table-meanings/v0";

/// A compiled logical meaning which a table-meaning relation may assign.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TableMeaning {
    /// Checked integer addition facts.
    Addition,
    /// Checked direct byte-length facts.
    ByteLength,
}

impl TableMeaning {
    const fn interpretation(self) -> &'static str {
        match self {
            Self::Addition => crate::addition::INTERPRETATION,
            Self::ByteLength => crate::byte_length::INTERPRETATION,
        }
    }
}

/// A validated relation which assigns compiled meanings to ordinary tables.
///
/// This first version permits one level of ownership only. The root catalog
/// interprets this relation; its rows interpret ordinary child tables.
#[derive(Debug)]
pub struct TableMeanings<'conn> {
    connection: &'conn Connection,
    name: String,
}

impl TableMeanings<'_> {
    /// Returns the physical name of this table-meaning relation.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Creates an owned addition relation.
    ///
    /// The child table and its meaning row are installed atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested
    /// transactions, or `SQLite` failures.
    pub fn create_addition(&self, name: &str) -> Result<Addition<'_>, TableMeaningError> {
        self.ensure_unowned(name)?;
        let transaction = self
            .connection
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateChildSnafu)?;
        addition::create_table(&transaction, name).context(CreateChildSnafu)?;
        self.record_meaning(&transaction, name, TableMeaning::Addition)?;
        transaction.commit().context(CreateChildSnafu)?;
        Ok(addition::wrapper(self.connection.neutron.sqlite(), name))
    }

    /// Creates an owned direct byte-length relation.
    ///
    /// The child table and its meaning row are installed atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested
    /// transactions, or `SQLite` failures.
    pub fn create_byte_lengths(&self, name: &str) -> Result<ByteLengths<'_>, TableMeaningError> {
        self.ensure_unowned(name)?;
        let transaction = self
            .connection
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateChildSnafu)?;
        byte_length::create_table(&transaction, name).context(CreateChildSnafu)?;
        self.record_meaning(&transaction, name, TableMeaning::ByteLength)?;
        transaction.commit().context(CreateChildSnafu)?;
        Ok(byte_length::wrapper(self.connection.neutron.sqlite(), name))
    }

    fn ensure_unowned(&self, name: &str) -> Result<(), TableMeaningError> {
        if catalog::name_is_reserved(name) {
            return Err(TableMeaningError::ReservedName {
                name: name.to_owned(),
            });
        }
        if catalog::entries(self.connection.neutron.sqlite())
            .map_err(map_catalog_error)?
            .iter()
            .any(|entry| entry.table == name)
        {
            return Err(TableMeaningError::AlreadyInterpreted {
                table: name.to_owned(),
            });
        }
        Ok(())
    }

    fn record_meaning(
        &self,
        sqlite: &sqlite::Connection,
        name: &str,
        meaning: TableMeaning,
    ) -> Result<(), TableMeaningError> {
        sqlite
            .execute(
                &format!(
                    "INSERT INTO {} (table_name, interpretation) VALUES (?1, ?2)",
                    catalog::main_table(&self.name)
                ),
                (name, meaning.interpretation()),
            )
            .context(CreateChildSnafu)?;
        Ok(())
    }

    /// Returns the compiled meanings assigned by this relation.
    ///
    /// # Errors
    ///
    /// Returns an error if the relation is malformed or contains an unknown
    /// meaning.
    pub fn meanings(&self) -> Result<Vec<(String, TableMeaning)>, TableMeaningError> {
        load_entries(self.connection.neutron.sqlite(), &self.name)?
            .into_iter()
            .map(|entry| {
                let meaning = match entry.interpretation.as_str() {
                    crate::addition::INTERPRETATION => TableMeaning::Addition,
                    crate::byte_length::INTERPRETATION => TableMeaning::ByteLength,
                    _ => {
                        return Err(TableMeaningError::UnknownMeaning {
                            table: entry.table,
                            interpretation: entry.interpretation,
                        });
                    }
                };
                Ok((entry.table, meaning))
            })
            .collect()
    }
}

impl Connection {
    /// Creates and root-catalogs a canonical table-meaning relation.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested transactions,
    /// or `SQLite` failures.
    pub fn create_table_meanings(
        &self,
        name: &str,
    ) -> Result<TableMeanings<'_>, TableMeaningError> {
        if catalog::name_is_reserved(name) {
            return Err(TableMeaningError::ReservedName {
                name: name.to_owned(),
            });
        }
        let quoted = catalog::main_table(name);
        let transaction = self
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateSnafu)?;
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {quoted} (
                    table_name TEXT NOT NULL PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT, WITHOUT ROWID;"
            ))
            .context(CreateSnafu)?;
        transaction
            .execute(
                "INSERT INTO main.cov_catalog (table_name, interpretation) VALUES (?1, ?2)",
                (name, INTERPRETATION),
            )
            .context(CreateSnafu)?;
        transaction.commit().context(CreateSnafu)?;
        Ok(TableMeanings {
            connection: self,
            name: name.to_owned(),
        })
    }

    /// Discovers and validates every root-catalogued table-meaning relation.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed catalogs, relations, or meanings.
    pub fn table_meaning_tables(&self) -> Result<Vec<TableMeanings<'_>>, TableMeaningError> {
        catalog::root_entries(self.neutron.sqlite())
            .map_err(map_catalog_error)?
            .into_iter()
            .filter(|entry| entry.interpretation == INTERPRETATION)
            .map(|entry| {
                validate_table(self.neutron.sqlite(), &entry.table)?;
                Ok(TableMeanings {
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
) -> Result<(), TableMeaningError> {
    if catalog::table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("table_name"), String::from("TEXT"), true, 1),
            (
                String::from("interpretation"),
                String::from("TEXT"),
                true,
                0,
            ),
        ]
        || catalog::table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(TableMeaningError::MalformedTable {
            table: name.to_owned(),
        });
    }
    Ok(())
}

pub(crate) fn load_entries(
    sqlite: &sqlite::Connection,
    name: &str,
) -> Result<Vec<catalog::Entry>, TableMeaningError> {
    sqlite
        .prepare(&format!(
            "SELECT table_name, interpretation FROM {} ORDER BY table_name",
            catalog::main_table(name)
        ))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok(catalog::Entry {
                table: row.get(0)?,
                interpretation: row.get(1)?,
            })
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)
}

fn map_catalog_error(error: catalog::CatalogError) -> TableMeaningError {
    match error {
        catalog::CatalogError::Sqlite { source } => TableMeaningError::Catalog { source },
        source => TableMeaningError::InvalidCatalog { source },
    }
}

/// Failure to construct, discover, or use a table-meaning relation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TableMeaningError {
    /// The requested name belongs to Nucleus or `SQLite`.
    #[snafu(display("table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected name.
        name: String,
    },

    /// Another catalog owner already interprets the table.
    #[snafu(display("table {table:?} is already interpreted"))]
    AlreadyInterpreted {
        /// Multiply interpreted table.
        table: String,
    },

    /// A relation row names a meaning unknown to this build.
    #[snafu(display("table {table:?} has unknown meaning {interpretation:?}"))]
    UnknownMeaning {
        /// Child table.
        table: String,
        /// Unknown interpretation.
        interpretation: String,
    },

    /// A table-meaning relation has the wrong representation.
    #[snafu(display("table-meaning relation {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// The root catalog is logically invalid.
    #[snafu(display("{source}"))]
    InvalidCatalog {
        /// Underlying catalog validation failure.
        source: catalog::CatalogError,
    },

    /// The root catalog could not be read.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The table-meaning relation could not be created.
    #[snafu(display("could not create table-meaning relation: {source}"))]
    Create {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// An owned child relation could not be created.
    #[snafu(display("could not create interpreted child table: {source}"))]
    CreateChild {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The table-meaning relation could not be scanned.
    #[snafu(display("could not scan table-meaning relation: {source}"))]
    Scan {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}
