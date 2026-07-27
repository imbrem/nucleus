use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::Connection;

const CATALOG: &str = "cov_catalog";
const ROWID_INTERPRETATION: &str = "cov.addition.rowid/v0";
const WITHOUT_ROWID_INTERPRETATION: &str = "cov.addition.without-rowid/v0";

/// Physical storage geometry of an addition relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AdditionLayout {
    /// Ordinary `SQLite` table with an implicit rowid.
    RowId,
    /// Composite-key table without a rowid.
    WithoutRowId,
}

impl AdditionLayout {
    const fn interpretation(self) -> &'static str {
        match self {
            Self::RowId => ROWID_INTERPRETATION,
            Self::WithoutRowId => WITHOUT_ROWID_INTERPRETATION,
        }
    }

    fn from_interpretation(value: &str) -> Option<Self> {
        match value {
            ROWID_INTERPRETATION => Some(Self::RowId),
            WITHOUT_ROWID_INTERPRETATION => Some(Self::WithoutRowId),
            _ => None,
        }
    }
}

/// One checked integer-addition fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdditionFact {
    /// Result term.
    pub tm: i64,
    /// Left operand.
    pub lhs: i64,
    /// Right operand.
    pub rhs: i64,
}

impl AdditionFact {
    /// Constructs a fact after checking arithmetic and equality.
    ///
    /// # Errors
    ///
    /// Returns an error on overflow or when `tm != lhs + rhs`.
    pub fn new(tm: i64, lhs: i64, rhs: i64) -> Result<Self, AdditionError> {
        let sum = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        if tm != sum {
            return Err(AdditionError::FalseFact { tm, lhs, rhs });
        }
        Ok(Self { tm, lhs, rhs })
    }

    /// Computes the result and constructs a fact.
    ///
    /// # Errors
    ///
    /// Returns an error when `lhs + rhs` overflows.
    pub fn sum(lhs: i64, rhs: i64) -> Result<Self, AdditionError> {
        let tm = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        Ok(Self { tm, lhs, rhs })
    }
}

/// One catalogued addition table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdditionTable {
    name: String,
    layout: AdditionLayout,
}

impl AdditionTable {
    /// Returns the physical table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the table's storage geometry.
    #[must_use]
    pub const fn layout(&self) -> AdditionLayout {
        self.layout
    }
}

impl Connection {
    /// Creates the persistent bootstrap catalog in an empty database.
    ///
    /// # Errors
    ///
    /// Returns an error if the catalog already exists or `SQLite` rejects it.
    pub fn create_persistent_catalog(&self) -> Result<(), AdditionError> {
        self.sqlite()
            .execute_batch(
                "CREATE TABLE cov_catalog (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT;",
            )
            .context(CatalogSnafu)
    }

    /// Creates and registers an addition table atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved names, duplicates, or `SQLite` failures.
    pub fn create_addition_table(
        &mut self,
        name: &str,
        layout: AdditionLayout,
    ) -> Result<AdditionTable, AdditionError> {
        if name == CATALOG || name.starts_with("cov_conn_") || name.starts_with("sqlite_") {
            return Err(AdditionError::ReservedName {
                name: name.to_owned(),
            });
        }
        let quoted = quote_identifier(name);
        let create = match layout {
            AdditionLayout::RowId => format!(
                "CREATE TABLE {quoted} (
                    tm INTEGER NOT NULL,
                    lhs INTEGER NOT NULL,
                    rhs INTEGER NOT NULL,
                    CHECK (typeof(lhs + rhs) = 'integer' AND tm = lhs + rhs)
                ) STRICT"
            ),
            AdditionLayout::WithoutRowId => format!(
                "CREATE TABLE {quoted} (
                    tm INTEGER NOT NULL,
                    lhs INTEGER NOT NULL,
                    rhs INTEGER NOT NULL,
                    PRIMARY KEY (tm, lhs, rhs),
                    CHECK (typeof(lhs + rhs) = 'integer' AND tm = lhs + rhs)
                ) STRICT, WITHOUT ROWID"
            ),
        };

        let transaction = self.sqlite_mut().transaction().context(CreateSnafu)?;
        transaction.execute(&create, ()).context(CreateSnafu)?;
        transaction
            .execute(
                "INSERT INTO cov_catalog (table_name, interpretation) VALUES (?1, ?2)",
                (name, layout.interpretation()),
            )
            .context(CreateSnafu)?;
        transaction.commit().context(CreateSnafu)?;
        Ok(AdditionTable {
            name: name.to_owned(),
            layout,
        })
    }

    /// Scans, structurally validates, and checks every catalogued addition row.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed catalogs, unknown interpretations,
    /// incompatible table geometry, invalid values, or false/overflowing rows.
    pub fn validate_addition_tables(&self) -> Result<Vec<AdditionTable>, AdditionError> {
        validate_catalog(self.sqlite())?;
        let mut statement = self
            .sqlite()
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
                let layout = AdditionLayout::from_interpretation(&interpretation).ok_or(
                    AdditionError::UnknownInterpretation {
                        table: name.clone(),
                        interpretation,
                    },
                )?;
                validate_addition_table(self.sqlite(), &name, layout)?;
                Ok(AdditionTable { name, layout })
            })
            .collect()
    }

    /// Inserts one already-checked fact into an addition table.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` rejects the row.
    pub fn insert_addition(
        &self,
        table: &AdditionTable,
        fact: AdditionFact,
    ) -> Result<(), AdditionError> {
        AdditionFact::new(fact.tm, fact.lhs, fact.rhs)?;
        let sql = format!(
            "INSERT INTO {} (tm, lhs, rhs) VALUES (?1, ?2, ?3)",
            quote_identifier(&table.name)
        );
        self.sqlite()
            .execute(&sql, (fact.tm, fact.lhs, fact.rhs))
            .context(InsertSnafu)?;
        Ok(())
    }

    /// Loads every fact from an addition table after checking it.
    ///
    /// # Errors
    ///
    /// Returns an error for `SQLite` failures, overflow, or a false row.
    pub fn addition_facts(
        &self,
        table: &AdditionTable,
    ) -> Result<Vec<AdditionFact>, AdditionError> {
        load_facts(self.sqlite(), &table.name)
    }
}

fn validate_catalog(connection: &sqlite::Connection) -> Result<(), AdditionError> {
    let columns = connection
        .prepare("PRAGMA table_info(cov_catalog)")
        .context(CatalogSnafu)?
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, bool>(3)?,
                row.get::<_, i64>(5)?,
            ))
        })
        .context(CatalogSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(CatalogSnafu)?;
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
    {
        return Err(AdditionError::MalformedCatalog);
    }
    Ok(())
}

fn validate_addition_table(
    connection: &sqlite::Connection,
    name: &str,
    layout: AdditionLayout,
) -> Result<(), AdditionError> {
    let quoted = quote_identifier(name);
    let columns = connection
        .prepare(&format!("PRAGMA table_info({quoted})"))
        .context(ScanSnafu)?
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, bool>(3)?,
                row.get::<_, i64>(5)?,
            ))
        })
        .context(ScanSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(ScanSnafu)?;
    let expected_pk = match layout {
        AdditionLayout::RowId => [0, 0, 0],
        AdditionLayout::WithoutRowId => [1, 2, 3],
    };
    let expected = ["tm", "lhs", "rhs"]
        .into_iter()
        .zip(expected_pk)
        .map(|(column, pk)| (String::from(column), String::from("INTEGER"), true, pk))
        .collect::<Vec<_>>();
    if columns != expected {
        return Err(AdditionError::MalformedTable {
            table: name.to_owned(),
        });
    }

    let (strict, without_rowid) = connection
        .query_row(
            "SELECT strict, wr FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [name],
            |row| Ok((row.get::<_, bool>(0)?, row.get::<_, bool>(1)?)),
        )
        .context(ScanSnafu)?;
    if !strict || without_rowid != (layout == AdditionLayout::WithoutRowId) {
        return Err(AdditionError::MalformedTable {
            table: name.to_owned(),
        });
    }
    load_facts(connection, name)?;
    Ok(())
}

fn load_facts(
    connection: &sqlite::Connection,
    name: &str,
) -> Result<Vec<AdditionFact>, AdditionError> {
    let mut statement = connection
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

/// Failure to construct or validate an addition relation.
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

    /// The row does not state a true addition.
    #[snafu(display("{tm} is not equal to {lhs} + {rhs}"))]
    FalseFact {
        /// Claimed result.
        tm: i64,
        /// Left operand.
        lhs: i64,
        /// Right operand.
        rhs: i64,
    },

    /// The requested table name is reserved.
    #[snafu(display("addition table name {name:?} is reserved"))]
    ReservedName {
        /// Rejected table name.
        name: String,
    },

    /// The persistent catalog is missing or malformed.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    MalformedCatalog,

    /// A catalog entry has an unknown interpretation.
    #[snafu(display("table {table:?} has unknown interpretation {interpretation:?}"))]
    UnknownInterpretation {
        /// Physical table name.
        table: String,
        /// Unrecognized interpretation.
        interpretation: String,
    },

    /// A catalogued table does not have its interpretation's exact geometry.
    #[snafu(display("addition table {table:?} has incompatible geometry"))]
    MalformedTable {
        /// Physical table name.
        table: String,
    },

    /// The persistent catalog could not be created or inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Catalog {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An addition table could not be created.
    #[snafu(display("could not create addition table: {source}"))]
    Create {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Addition tables could not be scanned.
    #[snafu(display("could not scan addition tables: {source}"))]
    Scan {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An addition fact could not be inserted.
    #[snafu(display("could not insert addition fact: {source}"))]
    Insert {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_multiple_layouts_and_rows() {
        let mut connection = Connection::open_in_memory().expect("open");
        connection
            .create_persistent_catalog()
            .expect("create catalog");
        let rowid = connection
            .create_addition_table("rowid_add", AdditionLayout::RowId)
            .expect("create rowid table");
        let compact = connection
            .create_addition_table("compact_add", AdditionLayout::WithoutRowId)
            .expect("create without-rowid table");
        connection
            .insert_addition(&rowid, AdditionFact::sum(20, 22).expect("sum"))
            .expect("insert rowid");
        connection
            .insert_addition(&compact, AdditionFact::sum(-7, 9).expect("sum"))
            .expect("insert compact");

        let tables = connection.validate_addition_tables().expect("validate");
        assert_eq!(tables, [compact, rowid]);
    }

    #[test]
    fn rejects_false_and_overflowing_facts() {
        assert!(matches!(
            AdditionFact::new(4, 2, 3),
            Err(AdditionError::FalseFact { .. })
        ));
        assert!(matches!(
            AdditionFact::sum(i64::MAX, 1),
            Err(AdditionError::Overflow { .. })
        ));
    }

    #[test]
    fn sqlite_constraints_reject_false_and_overflowing_rows() {
        let mut connection = Connection::open_in_memory().expect("open");
        connection
            .create_persistent_catalog()
            .expect("create catalog");
        let table = connection
            .create_addition_table("addition", AdditionLayout::RowId)
            .expect("create table");
        let quoted = quote_identifier(table.name());

        assert!(
            connection
                .sqlite()
                .execute(&format!("INSERT INTO {quoted} VALUES (4, 2, 3)"), ())
                .is_err()
        );
        assert!(
            connection
                .sqlite()
                .execute(
                    &format!("INSERT INTO {quoted} VALUES (?1, ?2, ?3)"),
                    (i64::MIN, i64::MAX, 1_i64)
                )
                .is_err()
        );
    }
}
