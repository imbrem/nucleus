//! Deliberately permeable SQL REPL protocol.
//!
//! Unlike trusted logical protocols, [`Repl`] permits arbitrary SQL and makes
//! no semantic claim about returned values. The protocol-specific wrappers in
//! this module own all access to the enclosed `SQLite` connection.

use std::collections::HashMap;
use std::sync::Arc;

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use crate::Connection;

mod image;

pub use image::ImageError;

/// Protocol state for an unrestricted SQL session.
///
/// Construction remains private so only Nucleus can enclose a connection as a
/// REPL after performing any admission required by future revisions.
pub struct Repl {
    images: HashMap<O256, Arc<[u8]>>,
}

/// An owned `SQLite` value suitable for transport across kernel boundaries.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// SQL `NULL`.
    Null,
    /// Signed 64-bit `SQLite` integer.
    Integer(i64),
    /// IEEE-754 double precision value.
    Real(f64),
    /// UTF-8 text.
    Text(String),
    /// Arbitrary bytes.
    Blob(Vec<u8>),
}

impl From<&Value> for sqlite::types::Value {
    fn from(value: &Value) -> Self {
        match value {
            Value::Null => Self::Null,
            Value::Integer(value) => Self::Integer(*value),
            Value::Real(value) => Self::Real(*value),
            Value::Text(value) => Self::Text(value.clone()),
            Value::Blob(value) => Self::Blob(value.clone()),
        }
    }
}

impl From<sqlite::types::Value> for Value {
    fn from(value: sqlite::types::Value) -> Self {
        match value {
            sqlite::types::Value::Null => Self::Null,
            sqlite::types::Value::Integer(value) => Self::Integer(value),
            sqlite::types::Value::Real(value) => Self::Real(value),
            sqlite::types::Value::Text(value) => Self::Text(value),
            sqlite::types::Value::Blob(value) => Self::Blob(value),
        }
    }
}

/// Complete owned rows returned by one SQL statement.
#[derive(Clone, Debug, PartialEq)]
pub struct QueryResult {
    /// Column names in statement order. Duplicate names are preserved.
    pub columns: Vec<String>,
    /// Rows in result order, with values in column order.
    pub rows: Vec<Vec<Value>>,
}

/// Result of running one SQL statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    /// The statement returned columns and zero or more rows.
    Rows(QueryResult),
    /// The statement returned no columns and changed this many rows.
    Changed(usize),
}

/// Prepared statement belonging to the [`Repl`] protocol.
///
/// This wrapper intentionally exposes no underlying rusqlite statement.
pub struct Statement<'connection> {
    inner: sqlite::Statement<'connection>,
}

impl Connection<Repl> {
    /// Opens a writable in-memory database as an unrestricted SQL session.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying `SQLite` connection cannot be opened.
    pub fn open_in_memory() -> Result<Self, covalence_neutron::ConnectionError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        Ok(Self::from_neutron(
            neutron,
            Repl {
                images: HashMap::new(),
            },
        ))
    }

    /// Prepares one SQL statement under the REPL protocol.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot prepare the statement.
    pub fn prepare<'connection>(
        &'connection mut self,
        sql: &str,
    ) -> sqlite::Result<Statement<'connection>> {
        let (neutron, _) = self.parts_mut();
        neutron
            .sqlite()
            .prepare(sql)
            .map(|inner| Statement { inner })
    }

    /// Runs one SQL statement and returns an owned result.
    ///
    /// # Errors
    ///
    /// Returns an error when the statement cannot be prepared or executed.
    pub fn run(&mut self, sql: &str, parameters: &[Value]) -> sqlite::Result<Outcome> {
        self.prepare(sql)?.run(parameters)
    }

    /// Executes a batch of SQL without returning rows.
    ///
    /// This is intended for explicit REPL setup and makes no atomicity claim.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` rejects any statement in the batch.
    pub fn execute_batch(&mut self, sql: &str) -> sqlite::Result<()> {
        let (neutron, _) = self.parts_mut();
        neutron.sqlite().execute_batch(sql)
    }
}

impl Statement<'_> {
    /// Returns this statement's column names in order.
    #[must_use]
    pub fn column_names(&self) -> Vec<String> {
        self.inner
            .column_names()
            .into_iter()
            .map(str::to_owned)
            .collect()
    }

    /// Executes a statement which returns no columns.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid parameters, execution failure, or a
    /// statement which returns rows.
    pub fn execute(&mut self, parameters: &[Value]) -> sqlite::Result<usize> {
        let parameters = parameters
            .iter()
            .map(sqlite::types::Value::from)
            .collect::<Vec<_>>();
        self.inner.execute(sqlite::params_from_iter(parameters))
    }

    /// Queries a statement and owns all rows before returning.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid parameters or while executing or decoding
    /// the query.
    pub fn query(&mut self, parameters: &[Value]) -> sqlite::Result<QueryResult> {
        let columns = self.column_names();
        let column_count = columns.len();
        let parameters = parameters
            .iter()
            .map(sqlite::types::Value::from)
            .collect::<Vec<_>>();
        let mut query = self.inner.query(sqlite::params_from_iter(parameters))?;
        let mut rows = Vec::new();
        while let Some(row) = query.next()? {
            let mut values = Vec::with_capacity(column_count);
            for index in 0..column_count {
                values.push(Value::from(row.get::<_, sqlite::types::Value>(index)?));
            }
            rows.push(values);
        }
        Ok(QueryResult { columns, rows })
    }

    /// Executes or queries this statement according to whether it has columns.
    ///
    /// # Errors
    ///
    /// Returns an error when execution or result decoding fails.
    pub fn run(&mut self, parameters: &[Value]) -> sqlite::Result<Outcome> {
        if self.inner.column_count() == 0 {
            self.execute(parameters).map(Outcome::Changed)
        } else {
            self.query(parameters).map(Outcome::Rows)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_statements_and_owns_all_sqlite_values() {
        let mut connection = Connection::<Repl>::open_in_memory().expect("open REPL");
        assert_eq!(
            connection
                .run(
                    "CREATE TABLE value(i INTEGER, r REAL, t TEXT, b BLOB, n TEXT)",
                    &[],
                )
                .expect("create table"),
            Outcome::Changed(0)
        );
        assert_eq!(
            connection
                .run(
                    "INSERT INTO value VALUES (?1, ?2, ?3, ?4, ?5)",
                    &[
                        Value::Integer(i64::MIN),
                        Value::Real(1.5),
                        Value::Text("hello".to_owned()),
                        Value::Blob(vec![0, 1, 255]),
                        Value::Null,
                    ],
                )
                .expect("insert row"),
            Outcome::Changed(1)
        );

        assert_eq!(
            connection
                .run("SELECT i, r, t, b, n FROM value", &[])
                .expect("query row"),
            Outcome::Rows(QueryResult {
                columns: ["i", "r", "t", "b", "n"].map(str::to_owned).to_vec(),
                rows: vec![vec![
                    Value::Integer(i64::MIN),
                    Value::Real(1.5),
                    Value::Text("hello".to_owned()),
                    Value::Blob(vec![0, 1, 255]),
                    Value::Null,
                ]],
            })
        );
    }

    #[test]
    fn preserves_duplicate_column_names() {
        let mut connection = Connection::<Repl>::open_in_memory().expect("open REPL");
        assert_eq!(
            connection.run("SELECT 1 AS x, 2 AS x", &[]).unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["x".to_owned(), "x".to_owned()],
                rows: vec![vec![Value::Integer(1), Value::Integer(2)]],
            })
        );
    }

    #[test]
    fn rejects_multiple_statements_in_single_run() {
        let mut connection = Connection::<Repl>::open_in_memory().expect("open REPL");
        assert!(connection.run("SELECT 1; SELECT 2", &[]).is_err());
    }
}
