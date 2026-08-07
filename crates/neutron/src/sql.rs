//! The opinionated layer over [`covalence_lib_sqlite`].
//!
//! `lib/sqlite` hides unsafety and little else: it exposes `prepare`, `bind`,
//! `step`, `column` with the same names and argument order as the C API. That
//! is the right shape for an auditable boundary and the wrong shape for
//! everyday use — three lines of ceremony to read one integer gets old fast,
//! and repeated by hand it is where mistakes come from.
//!
//! This module is where the ceremony goes, and it is deliberately *ours*
//! rather than general-purpose. It lowers exactly the Rust types this project
//! stores, in the way this project stores them, and adds nothing speculative:
//! no statement cache, no reflection, no trait-object rows. When a query needs
//! something not here, the answer is to write it here or to drop to the raw
//! API, not to reach for a general binding.

use std::ffi::CString;

use covalence_lib_sqlite::{Error, ResultCode, Statement, Step, ValueRef};

use crate::Connection;

/// A value this project stores in `SQLite`.
///
/// Deliberately the five storage classes and nothing else. There is no
/// conversion trait and no blanket impl, because every widening — `u32` to
/// `i64`, `bool` to `0`/`1` — is a decision that should be visible at the call
/// site rather than inferred.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Param<'a> {
    /// SQL `NULL`.
    Null,
    /// A 64-bit signed integer.
    Integer(i64),
    /// A double.
    Real(f64),
    /// UTF-8 text.
    Text(&'a str),
    /// An uninterpreted byte string.
    Blob(&'a [u8]),
}

impl From<i64> for Param<'_> {
    fn from(value: i64) -> Self {
        Self::Integer(value)
    }
}

impl<'a> From<&'a str> for Param<'a> {
    fn from(value: &'a str) -> Self {
        Self::Text(value)
    }
}

impl<'a> From<&'a [u8]> for Param<'a> {
    fn from(value: &'a [u8]) -> Self {
        Self::Blob(value)
    }
}

impl<T: Into<Self> + Copy> From<Option<T>> for Param<'_> {
    fn from(value: Option<T>) -> Self {
        value.map_or(Self::Null, Into::into)
    }
}

/// Copies `text` into a NUL-terminated C string.
///
/// `SQLite` names schemas, paths and VFSes with `char *`, so the conversion has
/// to happen somewhere. It happens here rather than in `lib/sqlite` because
/// what to do about an interior NUL is a policy question, and this is where the
/// policy lives: refuse it.
///
/// # Errors
///
/// Returns `SQLITE_MISUSE` when `text` contains a NUL byte.
pub fn c_string(text: &str) -> Result<CString, Error> {
    CString::new(text)
        .map_err(|_| Error::with_message(ResultCode::MISUSE, "string contains a NUL byte"))
}

/// Binds `params` to `statement` in order, starting at parameter 1.
///
/// # Errors
///
/// Returns an error when the count does not match what the statement expects,
/// or when `SQLite` rejects a binding.
pub fn bind_all(statement: &mut Statement, params: &[Param<'_>]) -> Result<(), Error> {
    let expected = statement.parameter_count();
    let supplied = i32::try_from(params.len())
        .map_err(|_| Error::with_message(ResultCode::MISUSE, "too many parameters"))?;
    if expected != supplied {
        return Err(Error::with_message(
            ResultCode::MISUSE,
            format!("statement takes {expected} parameters, {supplied} supplied"),
        ));
    }
    for (offset, param) in params.iter().enumerate() {
        // SQLite parameters are 1-based.
        let index = i32::try_from(offset + 1)
            .map_err(|_| Error::with_message(ResultCode::MISUSE, "too many parameters"))?;
        match *param {
            Param::Null => statement.bind_null(index)?,
            Param::Integer(value) => statement.bind_integer(index, value)?,
            Param::Real(value) => statement.bind_real(index, value)?,
            Param::Text(value) => statement.bind_text(index, value)?,
            Param::Blob(value) => statement.bind_blob(index, value)?,
        }
    }
    Ok(())
}

/// Querying, on the connection itself.
///
/// A second `impl` block rather than free functions, so that `lib/sqlite`
/// stays behind [`Connection`] instead of appearing in every call. The raw
/// handle is still reachable through
/// [`sqlite`](Connection::sqlite) for what this layer does not cover.
impl Connection {
    /// Prepares a single statement against this connection.
    ///
    /// # Errors
    ///
    /// Returns an error when `sql` holds no statement, holds more than one, or
    /// does not compile.
    pub fn prepare(&self, sql: &str) -> Result<Statement, Error> {
        Statement::prepare(self.sqlite(), sql)
    }

    /// Runs every statement in `sql`, discarding any rows.
    ///
    /// # Errors
    ///
    /// Returns the first error `SQLite` reports.
    pub fn execute_batch(&self, sql: &str) -> Result<(), Error> {
        Statement::execute_batch(self.sqlite(), sql)
    }

    /// Runs one statement to completion, returning the rows it changed.
    ///
    /// # Errors
    ///
    /// Returns an error when the statement does not compile, the parameters do
    /// not match, or execution fails.
    pub fn execute(&self, sql: &str, params: &[Param<'_>]) -> Result<i64, Error> {
        let mut statement = self.prepare(sql)?;
        bind_all(&mut statement, params)?;
        // A statement used for its effect may still return rows; drain them
        // rather than leaving the statement mid-scan.
        while statement.step()? == Step::Row {}
        Ok(self.sqlite().changes())
    }

    /// Runs one statement and maps its first row, if any.
    ///
    /// `None` means the query selected nothing. Rows beyond the first are not
    /// an error and are not read: a caller wanting exactly one should say so
    /// in SQL with `LIMIT 1`, which is clearer than a runtime check here.
    ///
    /// # Errors
    ///
    /// Returns an error when the statement does not compile, the parameters do
    /// not match, execution fails, or `map` fails.
    pub fn query_row<T>(
        &self,
        sql: &str,
        params: &[Param<'_>],
        map: impl FnOnce(&Row<'_>) -> Result<T, Error>,
    ) -> Result<Option<T>, Error> {
        let mut statement = self.prepare(sql)?;
        bind_all(&mut statement, params)?;
        if statement.step()? == Step::Done {
            return Ok(None);
        }
        map(&Row {
            statement: &statement,
        })
        .map(Some)
    }

    /// Runs one statement and maps every row.
    ///
    /// # Errors
    ///
    /// Returns an error when the statement does not compile, the parameters do
    /// not match, execution fails, or `map` fails on any row.
    pub fn query_all<T>(
        &self,
        sql: &str,
        params: &[Param<'_>],
        mut map: impl FnMut(&Row<'_>) -> Result<T, Error>,
    ) -> Result<Vec<T>, Error> {
        let mut statement = self.prepare(sql)?;
        bind_all(&mut statement, params)?;
        let mut rows = Vec::new();
        while statement.step()? == Step::Row {
            rows.push(map(&Row {
                statement: &statement,
            })?);
        }
        Ok(rows)
    }
}

/// One row of a result set.
///
/// Borrowed from the statement that produced it and valid only for the
/// duration of the mapping call.
pub struct Row<'a> {
    statement: &'a Statement,
}

impl Row<'_> {
    /// Returns the raw value at `index`.
    #[must_use]
    pub fn value(&self, index: i32) -> ValueRef<'_> {
        self.statement.column(index)
    }

    /// Reads an integer column.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is not an integer. A `NULL` is not
    /// silently zero — say `Option` if that is what the schema allows.
    pub fn integer(&self, index: i32) -> Result<i64, Error> {
        self.value(index).as_integer().ok_or_else(|| {
            Error::with_message(
                ResultCode::MISMATCH,
                format!("column {index} is not INTEGER"),
            )
        })
    }

    /// Reads an optional integer column.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is neither an integer nor `NULL`.
    pub fn integer_opt(&self, index: i32) -> Result<Option<i64>, Error> {
        let value = self.value(index);
        if value.is_null() {
            return Ok(None);
        }
        self.integer(index).map(Some)
    }

    /// Reads a text column.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is not text, or is not valid UTF-8.
    pub fn text(&self, index: i32) -> Result<String, Error> {
        self.value(index)
            .as_str()
            .map(ToOwned::to_owned)
            .ok_or_else(|| {
                Error::with_message(ResultCode::MISMATCH, format!("column {index} is not TEXT"))
            })
    }

    /// Reads an optional text column.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is neither text nor `NULL`.
    pub fn text_opt(&self, index: i32) -> Result<Option<String>, Error> {
        let value = self.value(index);
        if value.is_null() {
            return Ok(None);
        }
        self.text(index).map(Some)
    }

    /// Reads a blob column.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is not a blob.
    pub fn blob(&self, index: i32) -> Result<Vec<u8>, Error> {
        self.value(index)
            .as_bytes()
            .map(<[u8]>::to_vec)
            .ok_or_else(|| {
                Error::with_message(ResultCode::MISMATCH, format!("column {index} is not BLOB"))
            })
    }

    /// Reads a boolean column stored as an integer.
    ///
    /// # Errors
    ///
    /// Returns an error when the column is not an integer.
    pub fn boolean(&self, index: i32) -> Result<bool, Error> {
        self.integer(index).map(|value| value != 0)
    }
}

/// A transaction which rolls back unless it is committed.
///
/// Dropping without [`commit`](Self::commit) rolls back. That is the safe
/// default: an early return through `?` must not leave a half-applied change
/// behind, and making the *un*safe outcome require an explicit call is the only
/// arrangement where forgetting is harmless.
pub struct Transaction<'a> {
    connection: &'a Connection,
    finished: bool,
}

impl<'a> Transaction<'a> {
    /// Begins a deferred transaction.
    ///
    /// # Errors
    ///
    /// Returns an error when `BEGIN` fails, which includes a transaction
    /// already being open on this connection.
    pub fn begin(connection: &'a Connection) -> Result<Self, Error> {
        connection.execute_batch("BEGIN")?;
        Ok(Self {
            connection,
            finished: false,
        })
    }

    /// Borrows the underlying connection.
    #[must_use]
    pub const fn connection(&self) -> &'a Connection {
        self.connection
    }

    /// Commits.
    ///
    /// # Errors
    ///
    /// Returns an error when `COMMIT` fails. The transaction is considered
    /// finished either way: `SQLite` has already decided its fate, and
    /// rolling back afterwards would be a second, wrong decision.
    pub fn commit(mut self) -> Result<(), Error> {
        self.finished = true;
        self.connection.execute_batch("COMMIT")
    }

    /// Rolls back explicitly.
    ///
    /// # Errors
    ///
    /// Returns an error when `ROLLBACK` fails.
    pub fn rollback(mut self) -> Result<(), Error> {
        self.finished = true;
        self.connection.execute_batch("ROLLBACK")
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if !self.finished {
            // Nothing useful to do with a failure here: we are already
            // unwinding or returning, and the connection reports its own state.
            let _ = self.connection.execute_batch("ROLLBACK");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn connection() -> Connection {
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute_batch("CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT, data BLOB)")
            .unwrap();
        connection
    }

    #[test]
    fn execute_binds_and_reports_changes() {
        let connection = connection();
        let changed = connection
            .execute(
                "INSERT INTO t (id, name, data) VALUES (?1, ?2, ?3)",
                &[
                    Param::Integer(1),
                    Param::Text("one"),
                    Param::Blob(b"\x00\xff"),
                ],
            )
            .unwrap();
        assert_eq!(changed, 1);

        let name = connection
            .query_row(
                "SELECT name FROM t WHERE id = ?1",
                &[Param::Integer(1)],
                |row| row.text(0),
            )
            .unwrap();
        assert_eq!(name.as_deref(), Some("one"));
    }

    #[test]
    fn a_missing_row_is_none_not_an_error() {
        let connection = connection();
        let found = connection
            .query_row(
                "SELECT name FROM t WHERE id = ?1",
                &[Param::Integer(99)],
                |row| row.text(0),
            )
            .unwrap();
        assert!(found.is_none());
    }

    #[test]
    fn a_wrong_parameter_count_is_refused() {
        let connection = connection();
        let error = connection
            .execute("SELECT ?1, ?2", &[Param::Integer(1)])
            .unwrap_err();
        assert!(error.to_string().contains("takes 2 parameters"), "{error}");
    }

    #[test]
    fn null_round_trips_as_none() {
        let connection = connection();
        connection
            .execute(
                "INSERT INTO t (id, name) VALUES (?1, ?2)",
                &[Param::Integer(1), Param::Null],
            )
            .unwrap();
        let name = connection
            .query_row("SELECT name FROM t", &[], |row| row.text_opt(0))
            .unwrap()
            .unwrap();
        assert!(name.is_none());
    }

    #[test]
    fn a_type_mismatch_is_an_error_not_a_coercion() {
        let connection = connection();
        connection
            .execute(
                "INSERT INTO t (id, name) VALUES (?1, ?2)",
                &[Param::Integer(1), Param::Text("not a number")],
            )
            .unwrap();
        assert!(
            connection
                .query_row("SELECT name FROM t", &[], |row| row.integer(0))
                .is_err()
        );
    }

    #[test]
    fn query_all_maps_every_row() {
        let connection = connection();
        for id in 1..=3 {
            connection
                .execute("INSERT INTO t (id) VALUES (?1)", &[Param::Integer(id)])
                .unwrap();
        }
        let ids = connection
            .query_all("SELECT id FROM t ORDER BY id", &[], |row| row.integer(0))
            .unwrap();
        assert_eq!(ids, vec![1, 2, 3]);
    }

    #[test]
    fn a_committed_transaction_persists() {
        let connection = connection();
        let transaction = Transaction::begin(&connection).unwrap();
        transaction
            .connection()
            .execute("INSERT INTO t (id) VALUES (1)", &[])
            .unwrap();
        transaction.commit().unwrap();

        let count = connection
            .query_row("SELECT count(*) FROM t", &[], |row| row.integer(0))
            .unwrap();
        assert_eq!(count, Some(1));
    }

    #[test]
    fn a_dropped_transaction_rolls_back() {
        let connection = connection();
        {
            let transaction = Transaction::begin(&connection).unwrap();
            transaction
                .connection()
                .execute("INSERT INTO t (id) VALUES (1)", &[])
                .unwrap();
            // Dropped without committing: this is the path an early `?` takes.
        }
        let count = connection
            .query_row("SELECT count(*) FROM t", &[], |row| row.integer(0))
            .unwrap();
        assert_eq!(count, Some(0));
    }

    #[test]
    fn an_explicit_rollback_discards() {
        let connection = connection();
        let transaction = Transaction::begin(&connection).unwrap();
        transaction
            .connection()
            .execute("INSERT INTO t (id) VALUES (1)", &[])
            .unwrap();
        transaction.rollback().unwrap();

        let count = connection
            .query_row("SELECT count(*) FROM t", &[], |row| row.integer(0))
            .unwrap();
        assert_eq!(count, Some(0));
    }
}
