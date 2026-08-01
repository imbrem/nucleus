use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

use bytes::Bytes;
use covalence_neutron::Connection;

const CREATE_SQL: &str = include_str!("../sql/kv/create.sql");
const GET_SQL: &str = include_str!("../sql/kv/get.sql");
const INSERT_OR_REPLACE_SQL: &str = include_str!("../sql/kv/insert_or_replace.sql");
const REMOVE_SQL: &str = include_str!("../sql/kv/remove.sql");
const ITERATE_SQL: &str = include_str!("../sql/kv/iterate.sql");
const INSPECT_TABLE_SQL: &str = include_str!("../sql/kv/inspect_table.sql");
const INSPECT_COLUMNS_SQL: &str = include_str!("../sql/kv/inspect_columns.sql");

/// A prepared byte-keyed Nucleus table on a borrowed Neutron connection.
///
/// The table name is interpreted as one object name in `SQLite`'s `main`
/// schema, never as SQL or as a schema-qualified name. It is quoted before it
/// is substituted into the bundled SQL templates, so punctuation and quotes
/// in the name cannot add SQL syntax.
///
/// Opening a table checks that it is a strict, without-rowid table containing
/// exactly `key BLOB PRIMARY KEY` and `value BLOB NOT NULL`. This check is only
/// a point-in-time structural assertion. A caller can use
/// [`Connection::sqlite`] to change or replace the table afterwards, and
/// this wrapper does not assign application semantics or trust to its bytes.
#[derive(Debug)]
pub struct KvTable<'conn> {
    get: sqlite::Statement<'conn>,
    insert_or_replace: sqlite::Statement<'conn>,
    remove: sqlite::Statement<'conn>,
    iterate: sqlite::Statement<'conn>,
}

impl<'conn> KvTable<'conn> {
    /// Creates and opens a byte-keyed table in the `main` schema.
    ///
    /// Creation fails rather than adopting an object that already has the
    /// selected name. Use [`open`](Self::open) to validate and adopt an
    /// existing table.
    ///
    /// # Errors
    ///
    /// Returns an error when `table_name` is empty or contains a NUL, or when
    /// `SQLite` cannot create, validate, or prepare operations for the table.
    pub fn create(connection: &'conn Connection, table_name: &str) -> Result<Self, KvError> {
        let quoted_name = quote_table_name(table_name)?;
        connection
            .sqlite()
            .execute_batch(&instantiate(CREATE_SQL, &quoted_name))
            .context(CreateSnafu {
                table_name: table_name.to_owned(),
            })?;
        Self::open(connection, table_name)
    }

    /// Validates and opens an existing byte-keyed table in the `main` schema.
    ///
    /// # Errors
    ///
    /// Returns an error when `table_name` is empty or contains a NUL, when the
    /// named object does not have the canonical KV schema, or when `SQLite`
    /// cannot inspect or prepare operations for it.
    pub fn open(connection: &'conn Connection, table_name: &str) -> Result<Self, KvError> {
        let quoted_name = quote_table_name(table_name)?;
        validate_schema(connection, table_name)?;

        Ok(Self {
            get: prepare(connection, GET_SQL, &quoted_name, table_name)?,
            insert_or_replace: prepare(
                connection,
                INSERT_OR_REPLACE_SQL,
                &quoted_name,
                table_name,
            )?,
            remove: prepare(connection, REMOVE_SQL, &quoted_name, table_name)?,
            iterate: prepare(connection, ITERATE_SQL, &quoted_name, table_name)?,
        })
    }

    /// Returns the value stored for `key`, if present.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot execute the prepared lookup.
    pub fn get(&mut self, key: &[u8]) -> Result<Option<Bytes>, KvError> {
        self.get
            .query_row([key], |row| row.get::<_, Vec<u8>>(0))
            .optional()
            .context(GetSnafu)
            .map(|value| value.map(Bytes::from))
    }

    /// Inserts `key` and `value`, replacing the value of an existing key.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot execute the prepared write.
    pub fn insert_or_replace(&mut self, key: &[u8], value: &[u8]) -> Result<(), KvError> {
        self.insert_or_replace
            .execute((key, value))
            .context(InsertOrReplaceSnafu)?;
        Ok(())
    }

    /// Removes `key`, returning whether an entry existed.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot execute the prepared deletion.
    pub fn remove(&mut self, key: &[u8]) -> Result<bool, KvError> {
        self.remove
            .execute([key])
            .context(RemoveSnafu)
            .map(|changed| changed != 0)
    }

    /// Iterates over a snapshot of the entries in bytewise key order.
    ///
    /// The returned iterator keeps this handle mutably borrowed until it is
    /// dropped. Each item can independently report a `SQLite` decoding error.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot start the prepared query.
    pub fn scan(&mut self) -> Result<KvIter<'_>, KvError> {
        self.iterate
            .query([])
            .context(IterateSnafu)
            .map(|rows| KvIter { rows })
    }
}

/// One byte-keyed table entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KvEntry {
    /// Entry key.
    pub key: Bytes,
    /// Entry value.
    pub value: Bytes,
}

/// Streaming iterator over a prepared KV-table scan.
pub struct KvIter<'stmt> {
    rows: sqlite::Rows<'stmt>,
}

impl Iterator for KvIter<'_> {
    type Item = Result<KvEntry, KvError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.rows.next() {
            Ok(Some(row)) => Some(
                (|| {
                    Ok(KvEntry {
                        key: Bytes::from(row.get::<_, Vec<u8>>(0)?),
                        value: Bytes::from(row.get::<_, Vec<u8>>(1)?),
                    })
                })()
                .context(IterateSnafu),
            ),
            Ok(None) => None,
            Err(source) => Some(Err(KvError::Iterate { source })),
        }
    }
}

fn quote_table_name(table_name: &str) -> Result<String, KvError> {
    if table_name.is_empty() || table_name.contains('\0') {
        return Err(KvError::InvalidTableName);
    }
    Ok(format!("\"{}\"", table_name.replace('"', "\"\"")))
}

fn instantiate(template: &str, quoted_name: &str) -> String {
    template.replace("{table}", quoted_name)
}

fn prepare<'conn>(
    connection: &'conn Connection,
    template: &str,
    quoted_name: &str,
    table_name: &str,
) -> Result<sqlite::Statement<'conn>, KvError> {
    connection
        .sqlite()
        .prepare(&instantiate(template, quoted_name))
        .context(PrepareSnafu {
            table_name: table_name.to_owned(),
        })
}

fn validate_schema(connection: &Connection, table_name: &str) -> Result<(), KvError> {
    let table = connection
        .sqlite()
        .query_row(INSPECT_TABLE_SQL, [table_name], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, i64>(3)?,
            ))
        })
        .optional()
        .context(InspectSnafu {
            table_name: table_name.to_owned(),
        })?;
    if !matches!(table, Some((ref kind, 2, 1, 1)) if kind == "table") {
        return Err(KvError::InvalidSchema {
            table_name: table_name.to_owned(),
        });
    }

    let mut inspect = connection
        .sqlite()
        .prepare(INSPECT_COLUMNS_SQL)
        .context(InspectSnafu {
            table_name: table_name.to_owned(),
        })?;
    let columns = inspect
        .query_map([table_name], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, i64>(3)?,
                row.get::<_, i64>(4)?,
            ))
        })
        .context(InspectSnafu {
            table_name: table_name.to_owned(),
        })?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(InspectSnafu {
            table_name: table_name.to_owned(),
        })?;
    let expected = [
        ("key".to_owned(), "BLOB".to_owned(), 1, 1, 0),
        ("value".to_owned(), "BLOB".to_owned(), 1, 0, 0),
    ];
    if columns != expected {
        return Err(KvError::InvalidSchema {
            table_name: table_name.to_owned(),
        });
    }
    Ok(())
}

/// Failure to create, open, or access a byte-keyed table.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum KvError {
    /// The table name is empty or contains a NUL.
    #[snafu(display("KV table names must be non-empty and contain no NUL"))]
    InvalidTableName,

    /// The table could not be created.
    #[snafu(display("could not create KV table {table_name:?}: {source}"))]
    Create {
        /// Selected table name.
        table_name: String,
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The table could not be inspected.
    #[snafu(display("could not inspect KV table {table_name:?}: {source}"))]
    Inspect {
        /// Selected table name.
        table_name: String,
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The selected object is not a canonical byte-keyed table.
    #[snafu(display("object {table_name:?} does not have the canonical KV-table schema"))]
    InvalidSchema {
        /// Selected table name.
        table_name: String,
    },

    /// Prepared operations could not be compiled.
    #[snafu(display("could not prepare operations for KV table {table_name:?}: {source}"))]
    Prepare {
        /// Selected table name.
        table_name: String,
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A lookup failed.
    #[snafu(display("could not query KV table: {source}"))]
    Get {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An insert-or-replace failed.
    #[snafu(display("could not insert or replace a KV entry: {source}"))]
    InsertOrReplace {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A removal failed.
    #[snafu(display("could not remove a KV entry: {source}"))]
    Remove {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Iteration failed.
    #[snafu(display("could not iterate over a KV table: {source}"))]
    Iterate {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_neutron::CONNECTION_CATALOG;

    #[test]
    fn creates_and_operates_on_a_selected_table() {
        let connection = Connection::open_in_memory().expect("open connection");
        let mut table = KvTable::create(&connection, "application_kv").expect("create KV");

        assert_eq!(table.get(b"missing").expect("get missing"), None);
        table
            .insert_or_replace(b"beta", b"second")
            .expect("insert beta");
        table
            .insert_or_replace(b"alpha", b"first")
            .expect("insert alpha");
        table
            .insert_or_replace(b"beta", b"replacement")
            .expect("replace beta");

        assert_eq!(
            table.get(b"beta").expect("get beta"),
            Some(Bytes::from_static(b"replacement"))
        );
        assert_eq!(
            table
                .scan()
                .expect("start scan")
                .collect::<Result<Vec<_>, _>>()
                .expect("finish scan"),
            vec![
                KvEntry {
                    key: Bytes::from_static(b"alpha"),
                    value: Bytes::from_static(b"first"),
                },
                KvEntry {
                    key: Bytes::from_static(b"beta"),
                    value: Bytes::from_static(b"replacement"),
                },
            ]
        );

        assert!(table.remove(b"alpha").expect("remove present key"));
        assert!(!table.remove(b"alpha").expect("remove missing key"));
    }

    #[test]
    fn opens_an_existing_canonical_table() {
        let connection = Connection::open_in_memory().expect("open connection");
        {
            let mut created = KvTable::create(&connection, "persistent").expect("create KV");
            created
                .insert_or_replace(b"key", b"value")
                .expect("insert value");
        }

        let mut reopened = KvTable::open(&connection, "persistent").expect("reopen KV");
        assert_eq!(
            reopened.get(b"key").expect("get value"),
            Some(Bytes::from_static(b"value"))
        );
    }

    #[test]
    fn create_does_not_adopt_an_existing_table() {
        let connection = Connection::open_in_memory().expect("open connection");
        drop(KvTable::create(&connection, "unique_name").expect("first create"));

        assert!(matches!(
            KvTable::create(&connection, "unique_name"),
            Err(KvError::Create { .. })
        ));
        KvTable::open(&connection, "unique_name").expect("existing table remains valid");
    }

    #[test]
    fn treats_selected_name_as_one_literal_identifier() {
        let connection = Connection::open_in_memory().expect("open connection");
        let unusual_name = "odd.name\"; DROP TABLE cov_conn_catalog; --";
        let mut table = KvTable::create(&connection, unusual_name).expect("create quoted name");
        table
            .insert_or_replace(b"key", b"value")
            .expect("write quoted table");
        drop(table);

        let catalog_rows: i64 = connection
            .sqlite()
            .query_row(
                &format!("SELECT count(*) FROM temp.{CONNECTION_CATALOG}"),
                [],
                |row| row.get(0),
            )
            .expect("Neutron catalog still exists");
        assert!(catalog_rows > 0);
        assert_eq!(
            connection
                .sqlite()
                .query_row(
                    "SELECT count(*) FROM main.sqlite_schema WHERE name = ?1",
                    [unusual_name],
                    |row| row.get::<_, i64>(0),
                )
                .expect("query literal table name"),
            1
        );
    }

    #[test]
    fn rejects_invalid_names_before_using_sql() {
        let connection = Connection::open_in_memory().expect("open connection");
        assert!(matches!(
            KvTable::create(&connection, ""),
            Err(KvError::InvalidTableName)
        ));
        assert!(matches!(
            KvTable::open(&connection, "nul\0name"),
            Err(KvError::InvalidTableName)
        ));
    }

    #[test]
    fn rejects_missing_and_noncanonical_objects() {
        let connection = Connection::open_in_memory().expect("open connection");
        connection
            .sqlite()
            .execute_batch(
                "
                CREATE TABLE wrong_types (
                    key TEXT PRIMARY KEY,
                    value BLOB NOT NULL
                ) STRICT, WITHOUT ROWID;
                CREATE TABLE extra_column (
                    key BLOB PRIMARY KEY,
                    value BLOB NOT NULL,
                    metadata BLOB
                ) STRICT, WITHOUT ROWID;
                CREATE TABLE rowid_table (
                    key BLOB PRIMARY KEY,
                    value BLOB NOT NULL
                ) STRICT;
                CREATE VIEW kv_view AS SELECT x'' AS key, x'' AS value;
                ",
            )
            .expect("create noncanonical objects");

        for name in [
            "missing",
            "wrong_types",
            "extra_column",
            "rowid_table",
            "kv_view",
        ] {
            assert!(
                matches!(
                    KvTable::open(&connection, name),
                    Err(KvError::InvalidSchema { table_name }) if table_name == name
                ),
                "unexpected result for {name}"
            );
        }
    }
}
