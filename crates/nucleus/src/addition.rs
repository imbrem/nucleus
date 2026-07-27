use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::Connection;

const CATALOG: &str = "cov_catalog";
const INTERPRETATION: &str = "cov.addition/v0";

/// One proposed integer-addition fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdditionFact {
    /// Result.
    pub tm: i64,
    /// Left operand.
    pub lhs: i64,
    /// Right operand.
    pub rhs: i64,
}

impl AdditionFact {
    /// Checks and constructs `tm = lhs + rhs`.
    ///
    /// # Errors
    ///
    /// Returns an error if the addition overflows or the equality is false.
    pub fn new(tm: i64, lhs: i64, rhs: i64) -> Result<Self, AdditionError> {
        let sum = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        if tm != sum {
            return Err(AdditionError::False { tm, lhs, rhs });
        }
        Ok(Self { tm, lhs, rhs })
    }

    /// Computes and constructs `lhs + rhs`.
    ///
    /// # Errors
    ///
    /// Returns an error if the addition overflows.
    pub fn sum(lhs: i64, rhs: i64) -> Result<Self, AdditionError> {
        let tm = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        Ok(Self { tm, lhs, rhs })
    }
}

/// A validated addition relation in a Nucleus connection.
///
/// The wrapper is constructed from persistent catalog metadata and
/// encapsulates access to its physical `SQLite` table.
#[derive(Debug)]
pub struct Addition<'conn> {
    sqlite: &'conn sqlite::Connection,
    name: String,
}

impl Addition<'_> {
    /// Returns the physical table name recorded in the catalog.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Inserts one checked fact.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` rejects the insertion.
    pub fn insert(&self, fact: AdditionFact) -> Result<(), AdditionError> {
        let fact = AdditionFact::new(fact.tm, fact.lhs, fact.rhs)?;
        self.sqlite
            .execute(
                &format!(
                    "INSERT INTO {} (tm, lhs, rhs) VALUES (?1, ?2, ?3)",
                    quote_identifier(&self.name)
                ),
                (fact.tm, fact.lhs, fact.rhs),
            )
            .context(InsertSnafu)?;
        Ok(())
    }

    /// Loads and checks every fact in the relation.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed values, false facts, overflow, or a
    /// `SQLite` failure.
    pub fn facts(&self) -> Result<Vec<AdditionFact>, AdditionError> {
        load_facts(self.sqlite, &self.name)
    }
}

impl Connection {
    pub(crate) fn create_persistent_catalog(&self) -> Result<(), AdditionError> {
        self.neutron
            .sqlite()
            .execute_batch(
                "CREATE TABLE cov_catalog (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT, WITHOUT ROWID;",
            )
            .context(CatalogSnafu)
    }

    /// Creates, catalogs, and returns a canonical addition relation.
    ///
    /// Addition relations use one physical representation in this version:
    /// a strict `WITHOUT ROWID` table keyed by `(tm, lhs, rhs)`.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved or duplicate names, nested transactions,
    /// or `SQLite` failures.
    pub fn create_addition(&self, name: &str) -> Result<Addition<'_>, AdditionError> {
        validate_name(name)?;
        let quoted = quote_identifier(name);
        let transaction = self
            .neutron
            .sqlite()
            .unchecked_transaction()
            .context(CreateSnafu)?;
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {quoted} (
                    tm INTEGER NOT NULL,
                    lhs INTEGER NOT NULL,
                    rhs INTEGER NOT NULL,
                    PRIMARY KEY (tm, lhs, rhs),
                    CHECK (typeof(lhs + rhs) = 'integer' AND tm = lhs + rhs)
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
        Ok(Addition {
            sqlite: self.neutron.sqlite(),
            name: name.to_owned(),
        })
    }

    /// Discovers and validates every persistent addition relation.
    ///
    /// Each returned wrapper is constructed from catalog metadata only after
    /// its physical table and every existing row have passed validation.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed catalogs, unknown interpretations,
    /// incompatible tables, invalid rows, or `SQLite` failures.
    pub fn additions(&self) -> Result<Vec<Addition<'_>>, AdditionError> {
        let sqlite = self.neutron.sqlite();
        validate_catalog(sqlite)?;
        let mut statement = sqlite
            .prepare("SELECT table_name, interpretation FROM cov_catalog ORDER BY table_name")
            .context(ScanSnafu)?;
        let entries = statement
            .query_map((), |row| {
                Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?))
            })
            .context(ScanSnafu)?
            .collect::<sqlite::Result<Vec<_>>>()
            .context(ScanSnafu)?;

        entries
            .into_iter()
            .map(|(name, interpretation)| {
                if interpretation != INTERPRETATION {
                    return Err(AdditionError::UnknownInterpretation {
                        table: name,
                        interpretation,
                    });
                }
                validate_table(sqlite, &name)?;
                Ok(Addition { sqlite, name })
            })
            .collect()
    }
}

fn validate_name(name: &str) -> Result<(), AdditionError> {
    if name == CATALOG || name.starts_with("cov_conn_") || name.starts_with("sqlite_") {
        return Err(AdditionError::ReservedName {
            name: name.to_owned(),
        });
    }
    Ok(())
}

fn validate_catalog(sqlite: &sqlite::Connection) -> Result<(), AdditionError> {
    let columns = table_columns(sqlite, CATALOG).context(CatalogSnafu)?;
    if columns
        != [
            (String::from("table_name"), String::from("TEXT"), true, 1),
            (
                String::from("interpretation"),
                String::from("TEXT"),
                true,
                0,
            ),
        ]
        || table_flags(sqlite, CATALOG).context(CatalogSnafu)? != (true, true)
    {
        return Err(AdditionError::MalformedCatalog);
    }
    Ok(())
}

fn validate_table(sqlite: &sqlite::Connection, name: &str) -> Result<(), AdditionError> {
    if table_columns(sqlite, name).context(ScanSnafu)?
        != [
            (String::from("tm"), String::from("INTEGER"), true, 1),
            (String::from("lhs"), String::from("INTEGER"), true, 2),
            (String::from("rhs"), String::from("INTEGER"), true, 3),
        ]
        || table_flags(sqlite, name).context(ScanSnafu)? != (true, true)
    {
        return Err(AdditionError::MalformedTable {
            table: name.to_owned(),
        });
    }
    load_facts(sqlite, name)?;
    Ok(())
}

fn table_columns(
    sqlite: &sqlite::Connection,
    name: &str,
) -> sqlite::Result<Vec<(String, String, bool, i64)>> {
    sqlite
        .prepare(&format!("PRAGMA table_info({})", quote_identifier(name)))?
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, bool>(3)?,
                row.get::<_, i64>(5)?,
            ))
        })?
        .collect()
}

fn table_flags(sqlite: &sqlite::Connection, name: &str) -> sqlite::Result<(bool, bool)> {
    sqlite.query_row(
        "SELECT strict, wr FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
        [name],
        |row| Ok((row.get(0)?, row.get(1)?)),
    )
}

fn load_facts(sqlite: &sqlite::Connection, name: &str) -> Result<Vec<AdditionFact>, AdditionError> {
    let mut statement = sqlite
        .prepare(&format!(
            "SELECT tm, lhs, rhs FROM {} ORDER BY tm, lhs, rhs",
            quote_identifier(name)
        ))
        .context(ScanSnafu)?;
    let rows = statement
        .query_map((), |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, i64>(2)?,
            ))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    rows.into_iter()
        .map(|(tm, lhs, rhs)| AdditionFact::new(tm, lhs, rhs))
        .collect()
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to construct, discover, or use an addition relation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AdditionError {
    /// Integer addition overflowed or underflowed.
    #[snafu(display("integer addition {lhs} + {rhs} overflows"))]
    Overflow {
        /// Left operand.
        lhs: i64,
        /// Right operand.
        rhs: i64,
    },

    /// A proposed fact is false.
    #[snafu(display("{tm} is not equal to {lhs} + {rhs}"))]
    False {
        /// Claimed result.
        tm: i64,
        /// Left operand.
        lhs: i64,
        /// Right operand.
        rhs: i64,
    },

    /// The requested table name belongs to Nucleus or `SQLite`.
    #[snafu(display("addition table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected name.
        name: String,
    },

    /// The persistent catalog does not have the required representation.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    MalformedCatalog,

    /// A catalog entry has no known logical interpretation.
    #[snafu(display("table {table:?} has unknown interpretation {interpretation:?}"))]
    UnknownInterpretation {
        /// Physical table.
        table: String,
        /// Unrecognized interpretation.
        interpretation: String,
    },

    /// A catalogued addition relation has the wrong representation.
    #[snafu(display("addition table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table.
        table: String,
    },

    /// The persistent catalog could not be created or inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// `SQLite` failure.
        source: sqlite::Error,
    },

    /// An addition relation could not be created.
    #[snafu(display("could not create addition table: {source}"))]
    Create {
        /// `SQLite` failure.
        source: sqlite::Error,
    },

    /// Addition relations or facts could not be read.
    #[snafu(display("could not scan addition tables: {source}"))]
    Scan {
        /// `SQLite` failure.
        source: sqlite::Error,
    },

    /// A fact could not be inserted.
    #[snafu(display("could not insert addition fact: {source}"))]
    Insert {
        /// `SQLite` failure.
        source: sqlite::Error,
    },
}
