use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use std::collections::BTreeMap;

pub(crate) const NAME: &str = "cov_catalog";

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Entry {
    pub(crate) table: String,
    pub(crate) interpretation: String,
}

pub(crate) fn create(sqlite: &sqlite::Connection) -> Result<(), CatalogError> {
    sqlite
        .execute_batch(
            "CREATE TABLE main.cov_catalog (
                table_name TEXT PRIMARY KEY,
                interpretation TEXT NOT NULL
            ) STRICT, WITHOUT ROWID;",
        )
        .context(SqliteSnafu)
}

pub(crate) fn root_entries(sqlite: &sqlite::Connection) -> Result<Vec<Entry>, CatalogError> {
    validate(sqlite)?;
    sqlite
        .prepare("SELECT table_name, interpretation FROM main.cov_catalog ORDER BY table_name")
        .context(SqliteSnafu)?
        .query_map((), |row| {
            Ok(Entry {
                table: row.get(0)?,
                interpretation: row.get(1)?,
            })
        })
        .context(SqliteSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(SqliteSnafu)
}

pub(crate) fn entries(sqlite: &sqlite::Connection) -> Result<Vec<Entry>, CatalogError> {
    let roots = root_entries(sqlite)?;
    let mut entries = roots
        .iter()
        .map(|entry| {
            (
                entry.table.clone(),
                Entry {
                    table: entry.table.clone(),
                    interpretation: entry.interpretation.clone(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    for owner in roots
        .iter()
        .filter(|entry| entry.interpretation == crate::table_meaning::INTERPRETATION)
    {
        crate::table_meaning::validate_table(sqlite, &owner.table).map_err(|_| {
            CatalogError::MalformedMeaningTable {
                table: owner.table.clone(),
            }
        })?;
        for entry in crate::table_meaning::load_entries(sqlite, &owner.table).map_err(|_| {
            CatalogError::MalformedMeaningTable {
                table: owner.table.clone(),
            }
        })? {
            if entry.interpretation == crate::table_meaning::INTERPRETATION {
                return Err(CatalogError::NestedMeaningTable { table: entry.table });
            }
            let table = entry.table.clone();
            if entries.insert(table.clone(), entry).is_some() {
                return Err(CatalogError::DuplicateMeaning { table });
            }
        }
    }
    Ok(entries.into_values().collect())
}

pub(crate) fn name_is_reserved(name: &str) -> bool {
    name == NAME || name.starts_with("cov_conn_") || name.starts_with("sqlite_")
}

pub(crate) fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

pub(crate) fn main_table(name: &str) -> String {
    format!("main.{}", quote_identifier(name))
}

pub(crate) fn table_columns(
    sqlite: &sqlite::Connection,
    name: &str,
) -> sqlite::Result<Vec<(String, String, bool, i64)>> {
    sqlite
        .prepare(&format!(
            "PRAGMA main.table_info({})",
            quote_identifier(name)
        ))?
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

pub(crate) fn table_flags(sqlite: &sqlite::Connection, name: &str) -> sqlite::Result<(bool, bool)> {
    sqlite.query_row(
        "SELECT strict, wr FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
        [name],
        |row| Ok((row.get(0)?, row.get(1)?)),
    )
}

pub(crate) fn unique_indexes(
    sqlite: &sqlite::Connection,
    table: &str,
) -> sqlite::Result<Vec<Vec<String>>> {
    let indexes = sqlite
        .prepare(&format!(
            "PRAGMA main.index_list({})",
            quote_identifier(table)
        ))?
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, bool>(2)?,
                row.get::<_, String>(3)?,
            ))
        })?
        .collect::<sqlite::Result<Vec<_>>>()?;

    indexes
        .into_iter()
        .filter(|(_, unique, origin)| *unique && origin == "u")
        .map(|(index, _, _)| {
            sqlite
                .prepare(&format!(
                    "PRAGMA main.index_info({})",
                    quote_identifier(&index)
                ))?
                .query_map((), |row| row.get::<_, String>(2))?
                .collect()
        })
        .collect()
}

fn validate(sqlite: &sqlite::Connection) -> Result<(), CatalogError> {
    let columns = table_columns(sqlite, NAME).context(SqliteSnafu)?;
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
        || table_flags(sqlite, NAME).context(SqliteSnafu)? != (true, true)
    {
        return Err(CatalogError::Malformed);
    }
    Ok(())
}

#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CatalogError {
    /// The catalog does not have the canonical schema.
    #[snafu(display("persistent Nucleus catalog is malformed"))]
    Malformed,

    /// A table is interpreted by more than one catalog owner.
    #[snafu(display("table {table:?} has more than one semantic owner"))]
    DuplicateMeaning {
        /// Multiply owned table.
        table: String,
    },

    /// A first-pass table-meaning relation tried to define another one.
    #[snafu(display("nested table-meaning relation {table:?} is not supported"))]
    NestedMeaningTable {
        /// Nested table.
        table: String,
    },

    /// A root-catalogued table-meaning relation is malformed.
    #[snafu(display("table-meaning relation {table:?} is malformed"))]
    MalformedMeaningTable {
        /// Malformed relation.
        table: String,
    },

    /// The catalog could not be created or inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Sqlite {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}
