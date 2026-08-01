use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

use crate::{Bytes, Connection};

const CREATE_SQL: &str = include_str!("../sql/create_kv_table.sql");
const GET_SQL: &str = include_str!("../sql/get_kv.sql");
const INSERT_OR_REPLACE_SQL: &str = include_str!("../sql/insert_or_replace_kv.sql");
const REMOVE_SQL: &str = include_str!("../sql/remove_kv.sql");
const ITERATE_SQL: &str = include_str!("../sql/iterate_kv.sql");
const INSPECT_TABLE_SQL: &str = include_str!("../sql/inspect_kv_table.sql");
const INSPECT_COLUMNS_SQL: &str = include_str!("../sql/inspect_kv_columns.sql");

/// A prepared byte-keyed table on a borrowed Neutron connection.
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
/// Neutron does not assign application semantics or trust to its bytes.
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
