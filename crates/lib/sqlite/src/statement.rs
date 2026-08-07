#![allow(unsafe_code)]
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "SQLite's own constants and lengths are narrowed here, each at a single reviewed site"
)]
//! Prepared statements.

use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::fmt;
use std::ptr::{self, NonNull};
use std::rc::Rc;
use std::slice;

use crate::connection::{Connection, Handle};
use crate::error::{Error, ResultCode};
use crate::ffi;
use crate::value::{ValueRef, ValueType};

/// `SQLITE_UTF8` as `sqlite3_bind_text64` wants it.
const UTF8: u8 = ffi::SQLITE_UTF8 as u8;

/// What a call to [`Statement::step`] produced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Step {
    /// A row is available; read it with [`Statement::column`].
    Row,
    /// Execution finished.
    Done,
}

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
    raw: *mut ffi::sqlite3_stmt,
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
            raw: raw.as_ptr(),
            handle,
        }
    }

    /// Returns the raw statement pointer, or null once finalized.
    #[must_use]
    pub fn as_ptr(&self) -> *mut ffi::sqlite3_stmt {
        self.raw
    }

    /// Returns the SQL text this statement was compiled from.
    ///
    /// This is `sqlite3_sql`: the original text, with parameters unexpanded.
    /// Returns a `CStr` so callers can decide on encoding, length, or
    /// round-tripping the bytes back into SQLite.
    #[must_use]
    pub fn sql(&self) -> Option<&CStr> {
        // SAFETY: the statement is live, and `sqlite3_sql` returns either null
        // or a NUL-terminated string owned by the statement and valid for as
        // long as the statement is.
        let text = unsafe { ffi::sqlite3_sql(self.raw) };
        if text.is_null() {
            return None;
        }
        // SAFETY: `text` is a live NUL-terminated string, as above.
        Some(unsafe { CStr::from_ptr(text) })
    }

    /// Fails when the connection has been closed out from under the statement.
    fn usable(&self) -> Result<(), Error> {
        if self.handle.is_closed() {
            return Err(Error::with_message(
                ResultCode::MISUSE,
                "the connection this statement was prepared against is closed",
            ));
        }
        Ok(())
    }

    /// Turns a bind or step result code into an error carrying the connection's
    /// message.
    fn check(&self, code: c_int) -> Result<(), Error> {
        let code = ResultCode::new(code);
        if code.is_ok() {
            Ok(())
        } else {
            Err(self.handle.error(code))
        }
    }

    /// Returns the number of `?` parameters in the statement.
    #[must_use]
    pub fn parameter_count(&self) -> c_int {
        // SAFETY: the statement is live.
        unsafe { ffi::sqlite3_bind_parameter_count(self.raw) }
    }

    /// Returns the one-based index of a named parameter, if it has one.
    #[must_use]
    pub fn parameter_index(&self, name: &str) -> Option<c_int> {
        let name = CString::new(name).ok()?;
        // SAFETY: the statement is live and `name` is NUL-terminated and
        // outlives the call.
        let index = unsafe { ffi::sqlite3_bind_parameter_index(self.raw, name.as_ptr()) };
        (index != 0).then_some(index)
    }

    /// Binds `NULL` to the one-based parameter `index`.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed or the index is out of
    /// range.
    pub fn bind_null(&mut self, index: c_int) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: the statement is live; an out-of-range index is reported as
        // SQLITE_RANGE rather than being undefined.
        self.check(unsafe { ffi::sqlite3_bind_null(self.raw, index) })
    }

    /// Binds an integer to the one-based parameter `index`.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed or the index is out of
    /// range.
    pub fn bind_integer(&mut self, index: c_int, value: i64) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: as in `bind_null`.
        self.check(unsafe { ffi::sqlite3_bind_int64(self.raw, index, value) })
    }

    /// Binds a float to the one-based parameter `index`.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed or the index is out of
    /// range.
    pub fn bind_real(&mut self, index: c_int, value: f64) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: as in `bind_null`.
        self.check(unsafe { ffi::sqlite3_bind_double(self.raw, index, value) })
    }

    /// Binds UTF-8 text to the one-based parameter `index`.
    ///
    /// This is the explicit UTF-8 path (`SQLITE_UTF8`). For exact byte
    /// round-tripping of arbitrary text or blob data use [`Statement::bind_blob`]
    /// (or the [`Statement::bind`] helper).
    ///
    /// `SQLite` copies the text, so `value` need not outlive the call.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed, the index is out of
    /// range, or `SQLite` cannot allocate a copy.
    pub fn bind_text(&mut self, index: c_int, value: &str) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: `value` is a live byte range of exactly `value.len()` bytes,
        // and SQLITE_TRANSIENT tells SQLite to copy it before returning, so the
        // borrow does not outlive the call.
        self.check(unsafe {
            ffi::sqlite3_bind_text64(
                self.raw,
                index,
                value.as_ptr().cast::<c_char>(),
                value.len() as u64,
                ffi::SQLITE_TRANSIENT(),
                UTF8,
            )
        })
    }

    /// Binds a byte string to the one-based parameter `index`.
    ///
    /// `SQLite` copies the bytes, so `value` need not outlive the call.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed, the index is out of
    /// range, or `SQLite` cannot allocate the copy.
    pub fn bind_blob(&mut self, index: c_int, value: &[u8]) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: as in `bind_text`. A zero-length slice yields a dangling but
        // non-null pointer, which SQLite never dereferences when the length is
        // zero.
        self.check(unsafe {
            ffi::sqlite3_bind_blob64(
                self.raw,
                index,
                value.as_ptr().cast::<c_void>(),
                value.len() as u64,
                ffi::SQLITE_TRANSIENT(),
            )
        })
    }

    /// Binds a [`ValueRef`] to the one-based parameter `index`.
    ///
    /// Text and Blob variants are bound as blobs (exact bytes). Call
    /// [`Statement::bind_text`] directly if you need the UTF-8 text path.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed, the index is out of
    /// range, or `SQLite` cannot allocate a copy.
    pub fn bind(&mut self, index: c_int, value: ValueRef<'_>) -> Result<(), Error> {
        match value {
            ValueRef::Null => self.bind_null(index),
            ValueRef::Integer(value) => self.bind_integer(index, value),
            ValueRef::Real(value) => self.bind_real(index, value),
            ValueRef::Text(bytes) | ValueRef::Blob(bytes) => {
                // Exact byte round-trip for both Text and Blob variants.
                // Higher layers decide whether to interpret as UTF-8.
                self.bind_blob(index, bytes)
            }
        }
    }

    /// Advances the statement by one step.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection is closed or `SQLite` reports one.
    /// An error leaves the statement's transaction untouched; `SQLite` decides
    /// whether it is still live, and the caller decides whether to roll back.
    pub fn step(&mut self) -> Result<Step, Error> {
        self.usable()?;
        // SAFETY: the statement is live and belongs to an open connection.
        let code = ResultCode::new(unsafe { ffi::sqlite3_step(self.raw) });
        match code {
            ResultCode::ROW => Ok(Step::Row),
            ResultCode::DONE => Ok(Step::Done),
            _ => Err(self.handle.error(code)),
        }
    }

    /// Resets the statement so it can be run again, keeping its bindings.
    ///
    /// # Errors
    ///
    /// Returns the error the most recent execution ended with, if any.
    pub fn reset(&mut self) -> Result<(), Error> {
        self.usable()?;
        // SAFETY: the statement is live.
        self.check(unsafe { ffi::sqlite3_reset(self.raw) })
    }

    /// Sets every parameter back to `NULL`.
    pub fn clear_bindings(&mut self) {
        // SAFETY: the statement is live. `sqlite3_clear_bindings` cannot fail in
        // any way a caller can act on.
        unsafe { ffi::sqlite3_clear_bindings(self.raw) };
    }

    /// Returns the number of columns the statement produces.
    #[must_use]
    pub fn column_count(&self) -> c_int {
        // SAFETY: the statement is live.
        unsafe { ffi::sqlite3_column_count(self.raw) }
    }

    /// Returns the name assigned to a zero-based output column.
    #[must_use]
    pub fn column_name(&self, index: c_int) -> Option<&str> {
        // SAFETY: the statement is live. The returned string is owned by the
        // statement and outlives the borrow of `self`.
        let name = unsafe { ffi::sqlite3_column_name(self.raw, index) };
        if name.is_null() {
            return None;
        }
        // SAFETY: `name` is a live NUL-terminated string, as above.
        unsafe { CStr::from_ptr(name) }.to_str().ok()
    }

    /// Returns the storage class of a zero-based column in the current row.
    ///
    /// Out-of-range columns report [`ValueType::Null`], which is what `SQLite`
    /// does.
    #[must_use]
    pub fn column_type(&self, index: c_int) -> ValueType {
        // SAFETY: the statement is live.
        let code = unsafe { ffi::sqlite3_column_type(self.raw, index) };
        ValueType::from_raw(code).unwrap_or(ValueType::Null)
    }

    /// Borrows a zero-based column of the current row.
    ///
    /// The borrow ends at the next [`Statement::step`], [`Statement::reset`],
    /// or drop, which is what the `&self` borrow encodes. Only the accessor
    /// matching the column's storage class is called, so `SQLite` is never
    /// asked to convert a value and never invalidates a pointer this returned.
    #[must_use]
    pub fn column(&self, index: c_int) -> ValueRef<'_> {
        let raw = self.raw;
        match self.column_type(index) {
            ValueType::Null => ValueRef::Null,
            // SAFETY: the statement is live and the column holds an integer, so
            // `sqlite3_column_int64` reads it without converting.
            ValueType::Integer => {
                ValueRef::Integer(unsafe { ffi::sqlite3_column_int64(raw, index) })
            }
            // SAFETY: as above, for a float.
            ValueType::Real => ValueRef::Real(unsafe { ffi::sqlite3_column_double(raw, index) }),
            ValueType::Text => {
                // SAFETY: the column holds text, so this returns the stored
                // representation without converting. `sqlite3_column_bytes` is
                // called after the pointer accessor, as SQLite requires.
                let bytes = unsafe {
                    let data = ffi::sqlite3_column_text(raw, index);
                    Self::borrow(data.cast::<u8>(), ffi::sqlite3_column_bytes(raw, index))
                };
                ValueRef::Text(bytes)
            }
            ValueType::Blob => {
                // SAFETY: as above, for a blob.
                let bytes = unsafe {
                    let data = ffi::sqlite3_column_blob(raw, index);
                    Self::borrow(data.cast::<u8>(), ffi::sqlite3_column_bytes(raw, index))
                };
                ValueRef::Blob(bytes)
            }
        }
    }

    /// Views `length` bytes at `data` as a slice.
    ///
    /// # Safety
    ///
    /// When `length` is positive, `data` must point at that many initialised
    /// bytes that outlive the returned borrow.
    unsafe fn borrow<'a>(data: *const u8, length: c_int) -> &'a [u8] {
        let length = usize::try_from(length).unwrap_or(0);
        if data.is_null() || length == 0 {
            // SQLite returns a null pointer for a zero-length blob.
            return &[];
        }
        // SAFETY: guaranteed by the caller.
        unsafe { slice::from_raw_parts(data, length) }
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
        let raw = self.raw;
        let handle = self.handle.clone();
        std::mem::forget(self);
        let code = ResultCode::new(unsafe { ffi::sqlite3_finalize(raw) });
        if code.is_ok() {
            Ok(())
        } else {
            Err(handle.error(code))
        }
    }
}

impl Drop for Statement {
    fn drop(&mut self) {
        // SAFETY: `raw` is either a live statement owned by this value or null;
        // `sqlite3_finalize(NULL)` is a documented no-op. Finalizing is valid
        // even when the connection has already been closed (zombie state from
        // `sqlite3_close_v2`).
        unsafe { ffi::sqlite3_finalize(self.raw) };
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

#[cfg(not(any(target_arch = "wasm32")))]
unsafe impl Send for Statement {}

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
