#![allow(unsafe_code)]
//! Database connections.

use std::cell::Cell;
use std::ffi::{CStr, CString, c_char, c_int};
use std::fmt;
use std::ops::BitOr;
use std::ptr::{self, NonNull};
use std::rc::Rc;

use crate::error::{Error, ResultCode};
use crate::ffi;
use crate::statement::{Statement, Step};

unsafe extern "C" {
    /// Closes a connection, tolerating outstanding prepared statements.
    ///
    /// Neither backend generates a binding for this entry point:
    /// `libsqlite3-sys` blocklists it in `build.rs` and `sqlite-wasm-rs` simply
    /// omits it. Both compile it into the library they link, so it is declared
    /// here. This is also why `rusqlite` closes with `sqlite3_close` and must
    /// therefore keep statements borrowing their connection.
    ///
    /// <https://sqlite.org/c3ref/close.html>
    fn sqlite3_close_v2(db: *mut ffi::sqlite3) -> c_int;
}

/// Flags accepted by `sqlite3_open_v2`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct OpenFlags(c_int);

impl OpenFlags {
    /// Open for reading only.
    pub const READ_ONLY: Self = Self(ffi::SQLITE_OPEN_READONLY);
    /// Open for reading and writing.
    pub const READ_WRITE: Self = Self(ffi::SQLITE_OPEN_READWRITE);
    /// Create the database if it does not exist.
    pub const CREATE: Self = Self(ffi::SQLITE_OPEN_CREATE);
    /// Interpret the filename as a URI.
    pub const URI: Self = Self(ffi::SQLITE_OPEN_URI);
    /// Open a purely in-memory database.
    pub const MEMORY: Self = Self(ffi::SQLITE_OPEN_MEMORY);
    /// Use the multi-thread threading mode.
    pub const NO_MUTEX: Self = Self(ffi::SQLITE_OPEN_NOMUTEX);
    /// Use the serialized threading mode.
    pub const FULL_MUTEX: Self = Self(ffi::SQLITE_OPEN_FULLMUTEX);

    /// The flags [`Connection::open`] uses.
    pub const DEFAULT: Self = Self(ffi::SQLITE_OPEN_READWRITE | ffi::SQLITE_OPEN_CREATE);

    /// Wraps a raw flag word.
    #[must_use]
    pub const fn new(bits: c_int) -> Self {
        Self(bits)
    }

    /// Returns the raw flag word.
    #[must_use]
    pub const fn bits(self) -> c_int {
        self.0
    }
}

impl BitOr for OpenFlags {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

/// Shared ownership of an `sqlite3` handle.
///
/// The handle is closed when the last [`Connection`] and [`Statement`] sharing
/// it are dropped, or earlier if [`Connection::close`] is called explicitly.
pub(crate) struct Handle {
    db: NonNull<ffi::sqlite3>,
    closed: Cell<bool>,
}

impl Handle {
    /// Returns the raw handle.
    pub(crate) fn as_ptr(&self) -> *mut ffi::sqlite3 {
        self.db.as_ptr()
    }

    /// Reports whether `sqlite3_close_v2` has already been called.
    pub(crate) fn is_closed(&self) -> bool {
        self.closed.get()
    }

    /// Builds an [`Error`] for `code`, attaching `sqlite3_errmsg` when the
    /// connection is still usable.
    pub(crate) fn error(&self, code: ResultCode) -> Error {
        if self.closed.get() {
            return Error::new(code);
        }
        // SAFETY: the handle is live (it has not been closed) and
        // `sqlite3_errmsg` returns a NUL-terminated string owned by SQLite that
        // stays valid until the next call on this connection. It is copied here
        // before any other call can run.
        let message = unsafe {
            let text = ffi::sqlite3_errmsg(self.db.as_ptr());
            if text.is_null() {
                None
            } else {
                Some(CStr::from_ptr(text).to_string_lossy().into_owned())
            }
        };
        message.map_or_else(|| Error::new(code), |text| Error::with_message(code, text))
    }

    /// Closes the handle with `sqlite3_close_v2`, at most once.
    fn close(&self) -> ResultCode {
        if self.closed.replace(true) {
            return ResultCode::OK;
        }
        // SAFETY: `db` came from a successful `sqlite3_open_v2` and the `closed`
        // flag guarantees this is the only close. `sqlite3_close_v2` accepts a
        // handle with live statements: it zombifies the connection and frees it
        // once the last statement is finalized.
        ResultCode::new(unsafe { sqlite3_close_v2(self.db.as_ptr()) })
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        let _ = self.close();
    }
}

/// A connection to an `SQLite` database.
///
/// Cloning a connection shares one underlying `sqlite3` handle. Prepared
/// [`Statement`]s share it too, which is why they carry no lifetime.
///
/// A connection is neither `Send` nor `Sync`. Claiming `Send` would require
/// asserting `sqlite3_threadsafe() != 0`, which does not hold on
/// `wasm32-unknown-unknown`, where `sqlite-wasm-rs` compiles the amalgamation
/// with `SQLITE_THREADSAFE=0`. The refcount is a private field, so adding it
/// later is an internal change.
#[derive(Clone)]
pub struct Connection {
    handle: Rc<Handle>,
}

impl Connection {
    /// Opens a private, temporary in-memory database.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open_in_memory() -> Result<Self, Error> {
        Self::open_with_flags(":memory:", OpenFlags::DEFAULT | OpenFlags::MEMORY, None)
    }

    /// Opens `path` for reading and writing, creating it if necessary.
    ///
    /// `SQLite` filenames are UTF-8; callers holding a non-UTF-8 path must
    /// convert it themselves.
    ///
    /// # Errors
    ///
    /// Returns an error when `path` contains a NUL byte or `SQLite` cannot open
    /// the database.
    pub fn open(path: &str) -> Result<Self, Error> {
        Self::open_with_flags(path, OpenFlags::DEFAULT, None)
    }

    /// Opens `path` with explicit flags and an optional VFS name.
    ///
    /// # Errors
    ///
    /// Returns an error when `path` or `vfs` contains a NUL byte, or when
    /// `SQLite` cannot open the database.
    pub fn open_with_flags(path: &str, flags: OpenFlags, vfs: Option<&str>) -> Result<Self, Error> {
        let path = nul_terminated(path)?;
        let vfs = vfs.map(nul_terminated).transpose()?;
        let vfs_ptr = vfs.as_ref().map_or(ptr::null(), |name| name.as_ptr());
        let mut db: *mut ffi::sqlite3 = ptr::null_mut();
        // SAFETY: both strings are NUL-terminated and outlive the call, and
        // `db` points at a writable slot for the out-parameter.
        let code = ResultCode::new(unsafe {
            ffi::sqlite3_open_v2(path.as_ptr(), &raw mut db, flags.bits(), vfs_ptr)
        });
        let Some(db) = NonNull::new(db) else {
            // SQLite only leaves the handle null when it could not allocate.
            return Err(Error::new(if code.is_ok() {
                ResultCode::NOMEM
            } else {
                code
            }));
        };
        let handle = Rc::new(Handle {
            db,
            closed: Cell::new(false),
        });
        if code.is_ok() {
            Ok(Self { handle })
        } else {
            // `sqlite3_open_v2` returns a handle even on failure so the caller
            // can read the message; dropping `handle` closes it.
            Err(handle.error(code))
        }
    }

    /// Wraps a shared handle.
    pub(crate) const fn from_handle(handle: Rc<Handle>) -> Self {
        Self { handle }
    }

    /// Returns the raw handle.
    ///
    /// The pointer is valid while `self` is alive and has not been closed. It
    /// is the entry point for C-level facilities this crate does not wrap, such
    /// as VFS registration and `sqlite3_serialize`.
    #[must_use]
    pub fn as_ptr(&self) -> *mut ffi::sqlite3 {
        self.handle.as_ptr()
    }

    /// Reports whether [`Connection::close`] has already run.
    ///
    /// A closed connection may still be referenced by outstanding
    /// [`Statement`]s. Those statements can be finalized but not used.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.handle.is_closed()
    }

    /// Closes the connection with `sqlite3_close_v2`.
    ///
    /// This always succeeds, including when statements are still outstanding:
    /// `SQLite` marks the connection a zombie and frees it after the last
    /// statement is finalized. Any open transaction is rolled back.
    ///
    /// # Errors
    ///
    /// Returns an error only when `sqlite3_close_v2` itself reports one.
    pub fn close(self) -> Result<(), Error> {
        self.handle.close().ok()
    }

    /// Runs every statement in `sql`, discarding any rows they produce.
    ///
    /// Statements are prepared and stepped one at a time, so an error stops the
    /// batch at the statement that failed. Nothing here starts or ends a
    /// transaction: wrap the call in `BEGIN`/`COMMIT` when the batch must be
    /// atomic.
    ///
    /// # Errors
    ///
    /// Returns the first error `SQLite` reports while compiling or running the
    /// batch.
    pub fn execute_batch(&self, sql: &str) -> Result<(), Error> {
        let mut rest = sql;
        while !rest.is_empty() {
            let (statement, tail) = self.prepare_prefix(rest)?;
            rest = tail;
            let Some(mut statement) = statement else {
                continue;
            };
            while statement.step()? == Step::Row {}
            statement.finalize()?;
        }
        Ok(())
    }

    /// Returns the rowid of the most recent successful insert.
    #[must_use]
    pub fn last_insert_rowid(&self) -> i64 {
        // SAFETY: the handle is live for the duration of the call.
        unsafe { ffi::sqlite3_last_insert_rowid(self.handle.as_ptr()) }
    }

    /// Returns the number of rows the most recent statement changed.
    #[must_use]
    pub fn changes(&self) -> i64 {
        // SAFETY: the handle is live for the duration of the call.
        unsafe { ffi::sqlite3_changes64(self.handle.as_ptr()) }
    }

    /// Prepares a single SQL statement.
    ///
    /// `sql` must contain exactly one statement. Trailing text is rejected
    /// rather than silently ignored, so a caller cannot smuggle a second
    /// statement past a prepared query.
    ///
    /// # Errors
    ///
    /// Returns an error when `sql` contains a NUL byte, contains no statement,
    /// contains more than one statement, or fails to compile.
    pub fn prepare(&self, sql: &str) -> Result<Statement, Error> {
        let (statement, tail) = self.prepare_prefix(sql)?;
        let statement = statement.ok_or_else(|| {
            Error::with_message(ResultCode::MISUSE, "SQL text contains no statement")
        })?;
        // Whitespace and comments after the statement are not a second
        // statement; ask SQLite rather than guessing.
        if self.prepare_prefix(tail)?.0.is_some() {
            return Err(Error::with_message(
                ResultCode::MISUSE,
                "SQL text contains more than one statement",
            ));
        }
        Ok(statement)
    }

    /// Prepares the first statement in `sql`, returning it with the unconsumed
    /// remainder.
    ///
    /// The statement is `None` when the consumed prefix held only whitespace or
    /// comments, which is what `sqlite3_prepare_v2` reports for such input.
    ///
    /// # Errors
    ///
    /// Returns an error when `sql` contains a NUL byte or fails to compile.
    pub fn prepare_prefix<'sql>(
        &self,
        sql: &'sql str,
    ) -> Result<(Option<Statement>, &'sql str), Error> {
        if sql.as_bytes().contains(&0) {
            return Err(Error::with_message(
                ResultCode::MISUSE,
                "SQL text contains a NUL byte",
            ));
        }
        let length = c_int::try_from(sql.len()).map_err(|_| {
            Error::with_message(ResultCode::MISUSE, "SQL text is longer than c_int::MAX")
        })?;
        let mut raw: *mut ffi::sqlite3_stmt = ptr::null_mut();
        let mut tail: *const c_char = ptr::null();
        // SAFETY: `sql` is a live byte range of exactly `length` bytes, the two
        // out-parameters point at writable slots, and the handle is live.
        let code = ResultCode::new(unsafe {
            ffi::sqlite3_prepare_v2(
                self.handle.as_ptr(),
                sql.as_ptr().cast::<c_char>(),
                length,
                &raw mut raw,
                &raw mut tail,
            )
        });
        if !code.is_ok() {
            return Err(self.handle.error(code));
        }
        let consumed = if tail.is_null() {
            sql.len()
        } else {
            // SAFETY-free arithmetic: `tail` points into `sql`, so the
            // difference is a byte offset within it.
            (tail as usize).saturating_sub(sql.as_ptr() as usize)
        };
        let rest = sql.get(consumed..).unwrap_or("");
        // SAFETY: `raw` is either null (no statement in the prefix) or a
        // statement compiled by the call above and owned by us from here on.
        let statement = NonNull::new(raw)
            .map(|raw| unsafe { Statement::from_raw(raw, Rc::clone(&self.handle)) });
        Ok((statement, rest))
    }

    /// Returns `schema` as a complete database image.
    ///
    /// Wraps `sqlite3_serialize`. The bytes are copied out of the buffer
    /// `SQLite` allocated, and that buffer is freed before returning, so the
    /// result owns itself.
    ///
    /// # Errors
    ///
    /// Returns an error when `schema` contains a NUL byte, or when `SQLite`
    /// declines to serialize -- which it does for an unknown schema and when it
    /// cannot allocate.
    pub fn serialize(&self, schema: &str) -> Result<Vec<u8>, Error> {
        let schema = CString::new(schema)
            .map_err(|_| Error::with_message(ResultCode::MISUSE, "schema contains a NUL byte"))?;
        let mut size: ffi::sqlite3_int64 = 0;
        // SAFETY: the handle is live, `schema` is NUL-terminated, `size` points
        // at a writable slot, and passing no flags asks SQLite for a buffer it
        // allocated and hands to us.
        let raw = unsafe {
            ffi::sqlite3_serialize(self.handle.as_ptr(), schema.as_ptr(), &raw mut size, 0)
        };
        if raw.is_null() {
            return Err(self.handle.error(ResultCode::new(ffi::SQLITE_NOMEM)));
        }
        let len = usize::try_from(size).unwrap_or(0);
        // SAFETY: the call returned a buffer of exactly `size` bytes which
        // SQLite no longer touches and we now own.
        let bytes = unsafe { std::slice::from_raw_parts(raw.cast::<u8>(), len) }.to_vec();
        // SAFETY: `raw` came from SQLite's allocator and is not used again.
        unsafe { ffi::sqlite3_free(raw.cast()) };
        Ok(bytes)
    }

    /// Replaces `schema` with a complete database image.
    ///
    /// Wraps `sqlite3_deserialize`. The bytes are copied into a buffer from
    /// `SQLite`'s own allocator and handed over with `FREEONCLOSE`, so `SQLite`
    /// owns it from here and frees it when the database closes. The caller's
    /// slice is not retained.
    ///
    /// The result is read-only: `RESIZEABLE` is deliberately not passed, so a
    /// write is refused rather than silently reallocating an image intended to
    /// be immutable.
    ///
    /// # Errors
    ///
    /// Returns an error when `schema` contains a NUL byte, when the image
    /// exceeds `SQLite`'s size type, or when `SQLite` rejects it.
    pub fn deserialize(&self, schema: &str, bytes: &[u8]) -> Result<(), Error> {
        let schema = CString::new(schema)
            .map_err(|_| Error::with_message(ResultCode::MISUSE, "schema contains a NUL byte"))?;
        let size = ffi::sqlite3_int64::try_from(bytes.len())
            .map_err(|_| Error::with_message(ResultCode::MISUSE, "image is too large"))?;

        // SQLite must own the buffer, so it must come from SQLite's allocator.
        // SAFETY: requests `bytes.len()` bytes; a null return is the documented
        // out-of-memory signal and is checked below.
        let buffer = unsafe { ffi::sqlite3_malloc64(bytes.len() as u64) };
        if buffer.is_null() && !bytes.is_empty() {
            return Err(Error::new(ResultCode::new(ffi::SQLITE_NOMEM)));
        }
        // SAFETY: `buffer` is a fresh allocation of exactly `bytes.len()` bytes
        // and cannot overlap the caller's slice.
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), buffer.cast::<u8>(), bytes.len());
        }

        // SAFETY: the handle is live, `schema` is NUL-terminated, and `buffer`
        // holds exactly `size` bytes. FREEONCLOSE transfers the allocation to
        // SQLite, which is why it is not freed here on either path.
        let code = ResultCode::new(unsafe {
            ffi::sqlite3_deserialize(
                self.handle.as_ptr(),
                schema.as_ptr(),
                buffer.cast::<u8>(),
                size,
                size,
                ffi::SQLITE_DESERIALIZE_FREEONCLOSE,
            )
        });
        if !code.is_ok() {
            return Err(self.handle.error(code));
        }
        Ok(())
    }
}

impl fmt::Debug for Connection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Connection")
            .field("handle", &self.handle.as_ptr())
            .field("closed", &self.handle.is_closed())
            .finish()
    }
}

/// Copies `text` into a NUL-terminated C string.
fn nul_terminated(text: &str) -> Result<CString, Error> {
    CString::new(text)
        .map_err(|_| Error::with_message(ResultCode::MISUSE, "string contains a NUL byte"))
}

#[cfg(test)]
mod tests {
    use super::{Connection, OpenFlags};
    use crate::error::ResultCode;

    #[test]
    fn opens_and_closes_an_in_memory_database() {
        let connection = Connection::open_in_memory().expect("open");
        assert!(!connection.is_closed());
        connection.close().expect("close");
    }

    #[test]
    fn reports_the_reason_a_statement_did_not_compile() {
        let connection = Connection::open_in_memory().expect("open");
        let error = connection
            .prepare("SELECT * FROM absent")
            .expect_err("compile");
        assert_eq!(error.code(), ResultCode::new(1));
        assert!(error.message().is_some_and(|text| text.contains("absent")));
    }

    #[test]
    fn rejects_more_than_one_statement() {
        let connection = Connection::open_in_memory().expect("open");
        let error = connection
            .prepare("SELECT 1; SELECT 2")
            .expect_err("two statements");
        assert_eq!(error.code(), ResultCode::MISUSE);
    }

    #[test]
    fn accepts_a_trailing_semicolon_and_comment() {
        let connection = Connection::open_in_memory().expect("open");
        connection
            .prepare("SELECT 1; -- trailing comment")
            .expect("single statement");
    }

    #[test]
    fn reports_an_empty_prefix_without_a_statement() {
        let connection = Connection::open_in_memory().expect("open");
        let (statement, rest) = connection
            .prepare_prefix("   -- nothing here\n")
            .expect("prepare");
        assert!(statement.is_none());
        assert_eq!(rest, "");
    }

    #[test]
    fn splits_a_batch_into_statements() {
        let connection = Connection::open_in_memory().expect("open");
        let (first, rest) = connection
            .prepare_prefix("SELECT 1; SELECT 2")
            .expect("prepare first");
        assert!(first.is_some());
        assert_eq!(rest, " SELECT 2");
    }

    #[test]
    fn read_only_flags_reject_a_missing_file() {
        let error =
            Connection::open_with_flags("/nonexistent/nucleus.db", OpenFlags::READ_ONLY, None)
                .expect_err("open");
        assert_eq!(error.code().primary(), ResultCode::new(14));
    }

    #[test]
    fn a_statement_keeps_a_dropped_connection_alive() {
        let statement = {
            let connection = Connection::open_in_memory().expect("open");
            connection.prepare("SELECT 1").expect("prepare")
        };
        // The `Connection` value is gone, but the handle is not closed: the
        // statement still owns a reference to it.
        assert!(!statement.connection().is_closed());
        statement.finalize().expect("finalize");
    }

    #[test]
    fn an_explicitly_closed_connection_leaves_statements_finalizable() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = connection.prepare("SELECT 1").expect("prepare");
        // `sqlite3_close_v2` succeeds with a live statement and zombifies the
        // connection; the statement stays safe to finalize.
        connection.close().expect("close with a live statement");
        assert!(statement.connection().is_closed());
        statement.finalize().expect("finalize after close");
    }

    #[test]
    fn dropping_a_statement_after_its_connection_is_sound() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = connection.prepare("SELECT 1").expect("prepare");
        drop(connection);
        drop(statement);
    }
}
