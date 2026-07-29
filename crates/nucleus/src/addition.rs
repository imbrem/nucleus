use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Catalog, Thm};

const INTERPRETATION: &str = "cov.addition/v0";
const CREATE_SQL: &str = include_str!("../sql/addition/create.sql");
const INSERT_SQL: &str = include_str!("../sql/addition/insert.sql");
const CONTAINS_SQL: &str = include_str!("../sql/addition/contains.sql");
const SCAN_SQL: &str = include_str!("../sql/addition/scan.sql");
const REGISTER_SQL: &str = include_str!("../sql/addition/register.sql");
const CATALOG_TRIGGERS_SQL: &str = include_str!("../sql/addition/catalog_triggers.sql");

/// One integer-addition row.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AdditionFact {
    /// Claimed result.
    pub tm: i64,
    /// Left operand.
    pub lhs: i64,
    /// Right operand.
    pub rhs: i64,
}

impl AdditionFact {
    /// Applies the checked integer-addition rule.
    ///
    /// # Errors
    ///
    /// Returns an error if addition overflows or the claimed result is false.
    pub fn new(tm: i64, lhs: i64, rhs: i64) -> Result<Thm<Self>, AdditionError> {
        let sum = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        if tm != sum {
            return Err(AdditionError::False { tm, lhs, rhs });
        }
        Ok(Thm::new(Self { tm, lhs, rhs }))
    }

    /// Computes integer addition and returns its theorem.
    ///
    /// # Errors
    ///
    /// Returns an error if addition overflows.
    pub fn sum(lhs: i64, rhs: i64) -> Result<Thm<Self>, AdditionError> {
        let tm = lhs
            .checked_add(rhs)
            .ok_or(AdditionError::Overflow { lhs, rhs })?;
        Ok(Thm::new(Self { tm, lhs, rhs }))
    }
}

/// A trusted table maintained as true integer-addition facts.
#[derive(Debug)]
pub struct Addition<'conn> {
    insert: sqlite::Statement<'conn>,
    contains: sqlite::Statement<'conn>,
    scan: sqlite::Statement<'conn>,
}

impl Addition<'_> {
    /// Inserts an admitted addition fact.
    ///
    /// # Errors
    ///
    /// Returns an error if storage rejects the row.
    pub fn insert(&mut self, fact: &Thm<AdditionFact>) -> Result<(), AdditionError> {
        self.insert
            .execute((fact.tm, fact.lhs, fact.rhs))
            .context(StorageSnafu)?;
        Ok(())
    }

    /// Tests whether this trusted table contains `fact`.
    ///
    /// # Errors
    ///
    /// Returns an error if storage cannot answer the query.
    pub fn contains(&mut self, fact: &AdditionFact) -> Result<bool, AdditionError> {
        self.contains
            .query_row((fact.tm, fact.lhs, fact.rhs), |row| row.get(0))
            .context(StorageSnafu)
    }

    /// Loads the theorems maintained by this trusted table.
    ///
    /// # Errors
    ///
    /// Returns an error if storage cannot decode a row.
    pub fn facts(&mut self) -> Result<Vec<Thm<AdditionFact>>, AdditionError> {
        self.scan
            .query_map((), |row| {
                Ok(Thm::new(AdditionFact {
                    tm: row.get(0)?,
                    lhs: row.get(1)?,
                    rhs: row.get(2)?,
                }))
            })
            .context(StorageSnafu)?
            .collect::<Result<Vec<_>, _>>()
            .context(StorageSnafu)
    }
}

impl<'conn> Catalog<'conn> {
    /// Creates an empty table governed by integer addition.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved names, externally modified catalog
    /// machinery, duplicate objects, or storage failure.
    pub fn create_addition(&self, table_name: &str) -> Result<Addition<'conn>, AdditionError> {
        validate_user_table_name(table_name)?;
        ensure_catalog_has_no_triggers(self)?;
        let sqlite = self.connection.sqlite();
        let table = qualified_table(self.database_name(), table_name);
        let catalog = qualified_catalog(self);
        let transaction = sqlite.unchecked_transaction().context(StorageSnafu)?;
        transaction
            .execute_batch(&CREATE_SQL.replace("{table}", &table))
            .context(StorageSnafu)?;
        transaction
            .execute(
                &REGISTER_SQL.replace("{catalog}", &catalog),
                (table_name, INTERPRETATION),
            )
            .context(StorageSnafu)?;
        transaction.commit().context(StorageSnafu)?;

        Ok(Addition {
            insert: sqlite
                .prepare(&INSERT_SQL.replace("{table}", &table))
                .context(StorageSnafu)?,
            contains: sqlite
                .prepare(&CONTAINS_SQL.replace("{table}", &table))
                .context(StorageSnafu)?,
            scan: sqlite
                .prepare(&SCAN_SQL.replace("{table}", &table))
                .context(StorageSnafu)?,
        })
    }
}

fn validate_user_table_name(name: &str) -> Result<(), AdditionError> {
    if name.is_empty()
        || name.contains('\0')
        || name.starts_with("cov_db_")
        || name.starts_with("cov_conn_")
        || name.starts_with("sqlite_")
    {
        return Err(AdditionError::ReservedName {
            name: name.to_owned(),
        });
    }
    Ok(())
}

fn ensure_catalog_has_no_triggers(catalog: &Catalog<'_>) -> Result<(), AdditionError> {
    let count = catalog
        .connection
        .sqlite()
        .query_row(
            &CATALOG_TRIGGERS_SQL.replace(
                "{schema}",
                &crate::catalog::quote_identifier(catalog.database_name()),
            ),
            [if catalog.is_conn() {
                crate::CONNECTION_CATALOG
            } else {
                crate::DB_CATALOG
            }],
            |row| row.get::<_, i64>(0),
        )
        .context(StorageSnafu)?;
    if count != 0 {
        return Err(AdditionError::ModifiedCatalog);
    }
    Ok(())
}

fn qualified_table(database_name: &str, table_name: &str) -> String {
    format!(
        "{}.{}",
        crate::catalog::quote_identifier(database_name),
        crate::catalog::quote_identifier(table_name)
    )
}

fn qualified_catalog(catalog: &Catalog<'_>) -> String {
    qualified_table(
        catalog.database_name(),
        if catalog.is_conn() {
            crate::CONNECTION_CATALOG
        } else {
            crate::DB_CATALOG
        },
    )
}

/// Failure to derive or maintain trusted addition facts.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AdditionError {
    /// Integer addition overflowed or underflowed.
    #[snafu(display("integer addition {lhs} + {rhs} overflows"))]
    Overflow { lhs: i64, rhs: i64 },

    /// A proposed fact is false.
    #[snafu(display("{tm} is not equal to {lhs} + {rhs}"))]
    False { tm: i64, lhs: i64, rhs: i64 },

    /// Infrastructure and `SQLite`-reserved names cannot denote user tables.
    #[snafu(display("addition table name {name:?} is reserved"))]
    ReservedName { name: String },

    /// An existing trigger could violate atomic catalog registration.
    #[snafu(display("catalog was externally modified"))]
    ModifiedCatalog,

    /// The underlying storage operation failed.
    #[snafu(display("could not access trusted addition storage: {source}"))]
    Storage { source: sqlite::Error },
}
