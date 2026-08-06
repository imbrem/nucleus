#![allow(unsafe_code)]
//! Prepared statements.

use std::cell::Cell;
use std::ffi::CStr;
use std::fmt;
use std::ptr::{self, NonNull};
use std::rc::Rc;

use crate::connection::{Connection, Handle};
use crate::error::{Error, ResultCode};
use crate::ffi;

/// A prepared statement.
///
/// A statement carries no `'conn` lifetime. It holds a refcounted reference to
/// the connection it was compiled against, so the connection outlives every
/// statement prepared from it no matter what order the values are dropped in.
/// [`Connection::close`] may still be called early; the connection then becomes
/// an `SQLite` zombie and the statement can be finalized but not run.
pub struct Statement {
    /// Null once the statement has been finalized. `sqlite3_finalize` on a null
    /// pointer is a documented no-op, which is what makes [`Statement::finalize`]
    /// and [`Drop`] able to share one path without an extra flag.
    raw: Cell<*mut ffi::sqlite3_stmt>,
    handle: Rc<Handle>,
}

impl Statement {
    /// Adopts a statement compiled against `handle`.
    ///
    /// # Safety
    ///
    /// `raw` must be a live statement produced by `sqlite3_prepare_v2` on
    /// `handle`, and ownership of it must be transferred to the new value.
    pub(crate) unsafe fn from_raw(raw: NonNull<ffi::sqlite3_stmt>, handle: Rc<Handle>) -> Self {
        Self {
            raw: Cell::new(raw.as_ptr()),
            handle,
        }
    }

    /// Returns the raw statement pointer, or null once finalized.
    #[must_use]
    pub fn as_ptr(&self) -> *mut ffi::sqlite3_stmt {
        self.raw.get()
    }

    /// Returns the connection this statement was prepared against.
    ///
    /// The returned value shares the same `sqlite3` handle; it does not open a
    /// new one.
    #[must_use]
    pub fn connection(&self) -> Connection {
        Connection::from_handle(Rc::clone(&self.handle))
    }

    /// Returns the SQL text this statement was compiled from.
    ///
    /// This is `sqlite3_sql`: the original text, with parameters unexpanded.
    #[must_use]
    pub fn sql(&self) -> Option<&str> {
        // SAFETY: the statement is live, and `sqlite3_sql` returns either null
        // or a NUL-terminated string owned by the statement and valid for as
        // long as the statement is.
        let text = unsafe { ffi::sqlite3_sql(self.raw.get()) };
        if text.is_null() {
            return None;
        }
        // SAFETY: `text` is a live NUL-terminated string, as above.
        unsafe { CStr::from_ptr(text) }.to_str().ok()
    }

    /// Finalizes the statement and reports the result.
    ///
    /// Dropping a statement finalizes it too, discarding the result code. Use
    /// this when the code matters: `sqlite3_finalize` surfaces errors from the
    /// most recent execution.
    ///
    /// # Errors
    ///
    /// Returns the error the most recent execution of this statement ended
    /// with, if any.
    pub fn finalize(self) -> Result<(), Error> {
        let raw = self.raw.replace(ptr::null_mut());
        // SAFETY: `raw` is a live statement that this value owned, and taking it
        // out leaves null behind so the `Drop` below is a no-op.
        let code = ResultCode::new(unsafe { ffi::sqlite3_finalize(raw) });
        if code.is_ok() {
            Ok(())
        } else {
            Err(self.handle.error(code))
        }
    }
}

impl Drop for Statement {
    fn drop(&mut self) {
        // SAFETY: `raw` is either a live statement owned by this value or null,
        // and `sqlite3_finalize(NULL)` is a documented no-op. Finalizing is
        // valid even when the connection has already been closed: that is the
        // point of `sqlite3_close_v2`'s zombie state.
        unsafe { ffi::sqlite3_finalize(self.raw.get()) };
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Statement")
            .field("sql", &self.sql())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::connection::Connection;

    #[test]
    fn a_statement_reports_its_sql() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = connection.prepare("SELECT 1").expect("prepare");
        assert_eq!(statement.sql(), Some("SELECT 1"));
    }

    #[test]
    fn a_statement_hands_back_its_connection() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = connection.prepare("SELECT 1").expect("prepare");
        assert_eq!(statement.connection().as_ptr(), connection.as_ptr());
    }

    #[test]
    fn statements_outlive_every_connection_value() {
        // A plain `Vec<Statement>` with no lifetime parameter, built from a
        // connection that is dropped before the statements are used.
        let statements: Vec<_> = {
            let connection = Connection::open_in_memory().expect("open");
            ["SELECT 1", "SELECT 2", "SELECT 3"]
                .into_iter()
                .map(|sql| connection.prepare(sql).expect("prepare"))
                .collect()
        };
        assert_eq!(statements.len(), 3);
        assert!(!statements[0].connection().is_closed());
        for statement in statements {
            statement.finalize().expect("finalize");
        }
    }

    #[test]
    fn finalizing_twice_is_impossible_and_dropping_after_finalize_is_a_no_op() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = connection.prepare("SELECT 1").expect("prepare");
        // `finalize` consumes the statement, so the null left behind is only
        // ever observed by the `Drop` that immediately follows.
        statement.finalize().expect("finalize");
    }
}
