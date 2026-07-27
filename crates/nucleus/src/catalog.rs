use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

pub(crate) const NAME: &str = "cov_catalog";

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Entry {
    pub(crate) table: String,
    pub(crate) interpretation: String,
}

pub(crate) fn create(sqlite: &sqlite::Connection) -> Result<(), CatalogError> {
    sqlite
        .execute_batch(
            "CREATE TABLE cov_catalog (
                table_name TEXT PRIMARY KEY,
                interpretation TEXT NOT NULL
            ) STRICT, WITHOUT ROWID;",
        )
        .context(SqliteSnafu)
}

pub(crate) fn entries(sqlite: &sqlite::Connection) -> Result<Vec<Entry>, CatalogError> {
    validate(sqlite)?;
    sqlite
        .prepare("SELECT table_name, interpretation FROM cov_catalog ORDER BY table_name")
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

pub(crate) fn name_is_reserved(name: &str) -> bool {
    name == NAME || name.starts_with("cov_conn_") || name.starts_with("sqlite_")
}

pub(crate) fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

pub(crate) fn table_columns(
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

pub(crate) fn table_flags(sqlite: &sqlite::Connection, name: &str) -> sqlite::Result<(bool, bool)> {
    sqlite.query_row(
        "SELECT strict, wr FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
        [name],
        |row| Ok((row.get(0)?, row.get(1)?)),
    )
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

    /// The catalog could not be created or inspected.
    #[snafu(display("could not access persistent Nucleus catalog: {source}"))]
    Sqlite {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}
