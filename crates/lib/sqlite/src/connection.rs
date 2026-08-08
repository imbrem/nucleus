#![allow(unsafe_code)]
//! Database connections.

use std::ffi::{CStr, c_char, c_int};
use std::fmt;
use std::marker::PhantomData;
use std::ops::BitOr;
use std::ptr::{self, NonNull};

use crate::bytes::SqlBytes;
use crate::error::{Error, ResultCode};
use crate::ffi;
use crate::statement::Statement;

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

/// A borrowed `sqlite3` handle.
///
/// The same pointer a [`Connection`] owns, without the ownership. It exists so
/// a [`Statement`] can name the connection it was compiled against without
/// acquiring the right to close it.
///
/// It may outlive the owning [`Connection`]: dropping one calls
/// `sqlite3_close_v2`, which frees nothing while statements are outstanding.
/// The handle stays readable — that is what makes destructor order irrelevant
/// here — but a closed connection will refuse new work.
#[derive(Clone, Copy)]
pub struct ConnectionRef<'a> {
    db: NonNull<ffi::sqlite3>,
    /// Borrows whatever keeps the handle alive: a `Connection`, or a
    /// `Statement` compiled from it.
    borrow: PhantomData<&'a ()>,
}

impl fmt::Debug for ConnectionRef<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ConnectionRef")
            .field("db", &self.db)
            .finish()
    }
}

impl ConnectionRef<'_> {
    /// Borrows a raw handle.
    ///
    /// # Safety
    ///
    /// `db` must be a live `sqlite3` handle, open or closed, and must stay
    /// live for `'a`.
    #[must_use]
    pub const unsafe fn from_raw(db: NonNull<ffi::sqlite3>) -> Self {
        Self {
            db,
            borrow: PhantomData,
        }
    }

    /// Returns the raw handle.
    #[must_use]
    pub const fn as_ptr(self) -> *mut ffi::sqlite3 {
        self.db.as_ptr()
    }

    /// Returns `sqlite3_errmsg`, if there is one.
    ///
    /// Copied out immediately: `SQLite` owns the buffer and reuses it on the
    /// next call against this connection.
    #[must_use]
    pub fn message(self) -> Option<String> {
        // SAFETY: the handle is live for `'a` and `sqlite3_errmsg` returns a
        // NUL-terminated string owned by SQLite which stays valid until the
        // next call on this connection. It is copied here before any other
        // call can run.
        unsafe {
            let text = ffi::sqlite3_errmsg(self.db.as_ptr());
            if text.is_null() {
                None
            } else {
                Some(CStr::from_ptr(text).to_string_lossy().into_owned())
            }
        }
    }

    /// Builds an [`Error`] for `code`, attaching `sqlite3_errmsg`.
    #[must_use]
    pub fn error(self, code: ResultCode) -> Error {
        self.message()
            .map_or_else(|| Error::new(code), |text| Error::with_message(code, text))
    }
}

/// A connection to an `SQLite` database.
///
/// One connection, one handle, closed on drop. No sharing and no reference
/// count: `sqlite3_close_v2` defers freeing until the last statement is
/// finalized, which is the only coordination needed. That is also why
/// [`Statement`] carries no lifetime.
///
/// `Send` and `Sync` wherever `SQLite` is serialized, which is everywhere
/// except `wasm32-unknown-unknown` -- that target has no libc, so
/// `sqlite-wasm-rs` supplies its own single-threaded build. See the
/// `unsafe impl`s below.
pub struct Connection {
    db: NonNull<ffi::sqlite3>,
}

// SAFETY: two things have to hold, and both are enforced rather than assumed.
//
// - **The library is serialized.** `sqlite_serialized` is set by `build.rs`
//   from the same inputs the C build uses, so it cannot drift from the flag
//   the amalgamation was compiled with. In that mode `SQLite` takes a mutex on
//   the connection, and the documentation says it "can be safely used by
//   multiple threads with no restriction".
// - **This connection is serialized.** A per-connection `SQLITE_OPEN_NOMUTEX`
//   would drop it to multi-thread mode, where concurrent use of one connection
//   is not allowed. `open_with_flags` clears that bit and sets
//   `SQLITE_OPEN_FULLMUTEX`, so no caller can weaken it -- including through
//   `OpenFlags::new`, which takes a raw flag word.
//
// Nothing here hands out a borrow of `SQLite`'s own state: `message` copies
// the error string before returning, and `prepare_prefix`, `serialize`, and
// `deserialize` return owned values.
//
// SQL cannot reach any of this. The threading mode is settable at compile
// time, through `sqlite3_config` before initialization, and through the open
// flags -- and by no pragma. Arbitrary SQL can corrupt a database via
// `journal_mode`, `synchronous`, or `writable_schema`, which is the caller's
// business; it cannot create a data race. The one route from SQL to native
// code, `load_extension`, is refused unless a C call enables it, and
// `sqlite_refuses_to_load_extensions_from_sql` checks that it stays that way.
#[cfg(sqlite_serialized)]
#[allow(
    unsafe_code,
    reason = "serialized SQLite permits concurrent use of one connection"
)]
unsafe impl Send for Connection {}

#[cfg(sqlite_serialized)]
#[allow(
    unsafe_code,
    reason = "serialized SQLite permits concurrent use of one connection"
)]
unsafe impl Sync for Connection {}

impl Drop for Connection {
    fn drop(&mut self) {
        // SAFETY: `db` came from a successful `sqlite3_open_v2`, this is the
        // only owner, and `Connection::close` consumes `self` without running
        // this. `sqlite3_close_v2` accepts a handle with live statements.
        unsafe {
            sqlite3_close_v2(self.db.as_ptr());
        }
    }
}

impl Connection {
    /// Opens a private, temporary in-memory database.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open_in_memory() -> Result<Self, Error> {
        Self::open_with_flags(c":memory:", OpenFlags::DEFAULT | OpenFlags::MEMORY, None)
    }

    /// Opens `path` for reading and writing, creating it if necessary.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open(path: &CStr) -> Result<Self, Error> {
        Self::open_with_flags(path, OpenFlags::DEFAULT, None)
    }

    /// Opens `path` with explicit flags and an optional VFS name.
    ///
    /// Both strings are what `sqlite3_open_v2` takes: NUL-terminated and UTF-8.
    /// Getting there from a `Path` or a `String`, and deciding what an interior
    /// NUL means, is the caller's.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open_with_flags(
        path: &CStr,
        flags: OpenFlags,
        vfs: Option<&CStr>,
    ) -> Result<Self, Error> {
        // Serialized, whatever the caller asked for. `SQLITE_OPEN_NOMUTEX`
        // would put this one connection in multi-thread mode, and `Connection`
        // is `Sync` -- so a caller who reached it through `OpenFlags::new`
        // could hand out a type whose guarantee no longer holds. Clearing it
        // here is what makes that guarantee independent of the caller.
        let flags =
            OpenFlags(flags.bits() & !ffi::SQLITE_OPEN_NOMUTEX | ffi::SQLITE_OPEN_FULLMUTEX);
        let vfs_ptr = vfs.map_or(ptr::null(), CStr::as_ptr);
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
        let connection = Self { db };
        if code.is_ok() {
            Ok(connection)
        } else {
            // `sqlite3_open_v2` returns a handle even on failure so the caller
            // can read the message; dropping `connection` closes it.
            Err(connection.as_ref().error(code))
        }
    }

    /// Borrows the handle.
    #[must_use]
    pub const fn as_ref(&self) -> ConnectionRef<'_> {
        // SAFETY: `self` owns a live handle and outlives the borrow.
        unsafe { ConnectionRef::from_raw(self.db) }
    }

    /// Returns the raw handle.
    ///
    /// The pointer is valid while `self` is alive. It is the entry point for
    /// C-level facilities this crate does not wrap, such as VFS registration.
    #[must_use]
    pub const fn as_ptr(&self) -> *mut ffi::sqlite3 {
        self.db.as_ptr()
    }

    /// Builds an [`Error`] for `code`, attaching `SQLite`'s message.
    #[must_use]
    pub fn error(&self, code: ResultCode) -> Error {
        self.as_ref().error(code)
    }

    /// Closes the connection with `sqlite3_close_v2`.
    ///
    /// Succeeds even with statements outstanding — the handle is freed after
    /// the last one is finalized. Any open transaction is rolled back.
    ///
    /// # Errors
    ///
    /// Returns an error only when `sqlite3_close_v2` itself reports one.
    pub fn close(self) -> Result<(), Error> {
        // Take the handle out from under `Drop`, which would otherwise close a
        // second time.
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: `this` owns the handle and its destructor will not run.
        ResultCode::new(unsafe { sqlite3_close_v2(this.db.as_ptr()) }).ok()
    }

    /// Returns the rowid of the most recent successful insert.
    ///
    /// Wraps `sqlite3_last_insert_rowid`.
    #[must_use]
    pub fn last_insert_rowid(&self) -> i64 {
        // SAFETY: the handle is live for the duration of the call.
        unsafe { ffi::sqlite3_last_insert_rowid(self.db.as_ptr()) }
    }

    /// Returns the number of rows the most recent statement changed.
    ///
    /// Wraps `sqlite3_changes64`.
    #[must_use]
    pub fn changes(&self) -> i64 {
        // SAFETY: the handle is live for the duration of the call.
        unsafe { ffi::sqlite3_changes64(self.db.as_ptr()) }
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
                self.db.as_ptr(),
                sql.as_ptr().cast::<c_char>(),
                length,
                &raw mut raw,
                &raw mut tail,
            )
        });
        if !code.is_ok() {
            return Err(self.as_ref().error(code));
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
        let statement = NonNull::new(raw).map(|raw| unsafe { Statement::from_raw(raw) });
        Ok((statement, rest))
    }

    /// Returns `schema` as a complete database image.
    ///
    /// Wraps `sqlite3_serialize`. The buffer belongs to `SQLite`'s allocator,
    /// so it comes back as [`SqlBytes`] rather than a `Vec`: copying it is a
    /// decision for whoever wants an owned copy, not for this call. Handing it
    /// straight back to [`deserialize`](Self::deserialize) copies nothing at
    /// all.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` declines to serialize -- which it does
    /// for an unknown schema and when it cannot allocate.
    pub fn serialize(&self, schema: &CStr) -> Result<SqlBytes, Error> {
        let mut size: ffi::sqlite3_int64 = 0;
        // SAFETY: the handle is live, `schema` is NUL-terminated, `size` points
        // at a writable slot, and passing no flags asks SQLite for a buffer it
        // allocated and hands to us.
        let raw =
            unsafe { ffi::sqlite3_serialize(self.db.as_ptr(), schema.as_ptr(), &raw mut size, 0) };
        if raw.is_null() {
            return Err(self.error(ResultCode::NOMEM));
        }
        let len = usize::try_from(size).unwrap_or(0);
        // SAFETY: the call returned `len` bytes from SQLite's allocator and no
        // longer refers to them.
        Ok(unsafe { SqlBytes::from_raw(raw.cast::<u8>(), len) })
    }

    /// Replaces `schema` with a complete database image.
    ///
    /// Wraps `sqlite3_deserialize`. The image is taken by value because
    /// `SQLite` takes it by value: ownership passes with `FREEONCLOSE`, and
    /// from here on the buffer is `SQLite`'s to grow and to free. Nothing is
    /// copied, so a [`serialize`](Self::serialize) result can be handed
    /// straight back.
    ///
    /// The database is resizeable, so it can be written to like any other
    /// in-memory database. `SQLite` reallocates the buffer as it grows, which
    /// it can only do because the buffer came from its own allocator -- which
    /// is precisely what holding a [`SqlBytes`] means.
    ///
    /// # Errors
    ///
    /// Returns an error when the image exceeds `SQLite`'s size type or when
    /// `SQLite` rejects it. The image is consumed either way: on failure
    /// `sqlite3_deserialize` frees it itself, since it was given ownership.
    pub fn deserialize(&self, schema: &CStr, image: SqlBytes) -> Result<(), Error> {
        let size = ffi::sqlite3_int64::try_from(image.len())
            .map_err(|_| Error::with_message(ResultCode::MISUSE, "image is too large"))?;
        let (data, _) = image.into_raw();

        // SAFETY: the handle is live, `schema` is NUL-terminated, and `data` is
        // an allocation of exactly `size` bytes from SQLite's allocator whose
        // ownership `FREEONCLOSE` transfers -- including on the error path,
        // where `sqlite3_deserialize` frees it before returning. That is why
        // nothing is freed here.
        let code = ResultCode::new(unsafe {
            ffi::sqlite3_deserialize(
                self.db.as_ptr(),
                schema.as_ptr(),
                data,
                size,
                size,
                ffi::SQLITE_DESERIALIZE_FREEONCLOSE | ffi::SQLITE_DESERIALIZE_RESIZEABLE,
            )
        });
        code.ok().map_err(|_| self.as_ref().error(code))
    }
}

impl fmt::Debug for Connection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Connection")
            .field("db", &self.db)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{Connection, OpenFlags};
    use crate::error::ResultCode;
    use crate::statement::{Statement, Step};
    use crate::value::ValueRef;

    /// The whole safety argument, checked against the library that actually
    /// linked. If `build.rs` and the C build ever disagree, this fails rather
    /// than the program racing.
    #[test]
    fn the_serialized_cfg_matches_the_linked_library() {
        #[expect(unsafe_code, reason = "reads SQLite's compiled threading mode")]
        // SAFETY: takes no arguments and reads a compile-time constant.
        let mode = unsafe { crate::ffi::sqlite3_threadsafe() };
        assert_eq!(
            cfg!(sqlite_serialized),
            mode != 0,
            "build.rs said serialized={}, but sqlite3_threadsafe() is {mode}",
            cfg!(sqlite_serialized),
        );
    }

    /// The only route from SQL to native code, and it stays shut.
    ///
    /// An extension is arbitrary code in this process, so if this ever starts
    /// succeeding then `Send` and `Sync` are the least of it.
    ///
    /// The refusal has two shapes and this accepts either. Where `dlopen`
    /// exists, `libsqlite3-sys` passes `SQLITE_ENABLE_LOAD_EXTENSION=1`, so the
    /// SQL function is registered and declines at run time -- `SQLite`'s own
    /// default, not our configuration. On WASI there is no `dlopen`, so the
    /// function is never registered and the statement does not even compile.
    /// The second is strictly the stronger refusal; what matters is that
    /// neither one loads anything.
    #[test]
    fn sqlite_refuses_to_load_extensions_from_sql() {
        let connection = Connection::open_in_memory().expect("open");
        let error = match Statement::prepare(&connection, "SELECT load_extension('/tmp/x.so')") {
            Ok(mut statement) => statement
                .step()
                .expect_err("load_extension must not be callable from SQL"),
            Err(refused_at_compile_time) => refused_at_compile_time,
        };
        let message = error.to_string();
        assert!(
            message.contains("not authorized") || message.contains("no such function"),
            "unexpected refusal: {message}"
        );
    }

    /// A connection is serialized whatever the caller asked for, which is what
    /// `Sync` rests on.
    ///
    /// `sqlite3_db_mutex` is the observation: it returns the mutex serializing
    /// the connection, and a null pointer when the connection is in
    /// multi-thread or single-thread mode. So asking for `SQLITE_OPEN_NOMUTEX`
    /// and still getting a mutex back is exactly the guarantee, read off the
    /// connection `SQLite` actually built.
    ///
    /// Only meaningful where mutexes are compiled in at all; that is the same
    /// condition the `unsafe impl`s carry.
    #[cfg(sqlite_serialized)]
    #[test]
    fn nomutex_cannot_be_asked_for() {
        let asked = OpenFlags::new(crate::ffi::SQLITE_OPEN_NOMUTEX) | OpenFlags::DEFAULT;
        let connection = Connection::open_with_flags(c":memory:", asked, None).expect("open");
        // SAFETY: the handle is live for the call, which only reads the mutex
        // pointer SQLite stored on it.
        let mutex = unsafe { crate::ffi::sqlite3_db_mutex(connection.as_ptr()) };
        assert!(
            !mutex.is_null(),
            "asked for NOMUTEX and got a connection without a mutex, so `Sync` does not hold"
        );
    }

    /// The impls exist wherever the cfg does, which is the whole contract.
    ///
    /// Static, so it holds on targets that have no threads to check it with.
    #[cfg(sqlite_serialized)]
    #[test]
    fn a_serialized_connection_is_send_and_sync() {
        const fn assert_send_and_sync<T: Send + Sync>() {}
        assert_send_and_sync::<Connection>();
    }

    /// And `Sync` survives one connection being used from another thread.
    ///
    /// Not on `wasm32-wasip1`, which is serialized -- the impls are there and
    /// the assertion above covers them -- but has no threads in preview 1, so
    /// `thread::scope` aborts rather than reporting anything. Nothing can race
    /// there, so there is nothing this would catch.
    #[cfg(all(sqlite_serialized, not(target_family = "wasm")))]
    #[test]
    fn a_serialized_connection_crosses_threads() {
        let connection = Connection::open_in_memory().expect("open");
        std::thread::scope(|scope| {
            scope.spawn(|| {
                let mut statement = Statement::prepare(&connection, "SELECT 1").expect("compile");
                assert_eq!(statement.step().expect("step"), Step::Row);
            });
        });
    }

    #[test]
    fn opens_and_closes_an_in_memory_database() {
        let connection = Connection::open_in_memory().expect("open");
        connection.close().expect("close");
    }

    #[test]
    fn reports_the_reason_a_statement_did_not_compile() {
        let connection = Connection::open_in_memory().expect("open");
        let error = connection
            .prepare_prefix("SELECT * FROM absent")
            .expect_err("compile");
        assert_eq!(error.code(), ResultCode::new(1));
        assert!(error.message().is_some_and(|text| text.contains("absent")));
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
            Connection::open_with_flags(c"/nonexistent/nucleus.db", OpenFlags::READ_ONLY, None)
                .expect_err("open");
        assert_eq!(error.code().primary(), ResultCode::new(14));
    }

    #[test]
    fn a_statement_outlives_a_dropped_connection() {
        let mut statement = {
            let connection = Connection::open_in_memory().expect("open");
            Statement::prepare(&connection, "SELECT 1").expect("compile")
        };
        // The `Connection` is gone and `sqlite3_close_v2` has run, but the
        // handle is not freed: this statement is what keeps it alive.
        assert_eq!(statement.step().expect("step"), Step::Row);
        assert_eq!(statement.column(0), ValueRef::Integer(1));
        statement.finalize().expect("finalize");
    }

    #[test]
    fn an_explicitly_closed_connection_leaves_statements_finalizable() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = Statement::prepare(&connection, "SELECT 1").expect("compile");
        // `sqlite3_close_v2` succeeds with a live statement and zombifies the
        // connection; the statement stays safe to finalize.
        connection.close().expect("close with a live statement");
        statement.finalize().expect("finalize after close");
    }

    #[test]
    fn dropping_a_statement_after_its_connection_is_sound() {
        let connection = Connection::open_in_memory().expect("open");
        let statement = Statement::prepare(&connection, "SELECT 1").expect("compile");
        drop(connection);
        drop(statement);
    }

    #[test]
    fn a_deserialized_image_is_writable() {
        let source = Connection::open_in_memory().expect("open");
        for sql in [
            "CREATE TABLE example (value INTEGER) STRICT",
            "INSERT INTO example VALUES (7)",
        ] {
            let mut statement = Statement::prepare(&source, sql).expect("compile");
            while statement.step().expect("step") == Step::Row {}
        }
        let image = source.serialize(c"main").expect("serialize");
        assert!(!image.is_empty());

        // No copy: the buffer SQLite allocated goes straight back to SQLite.
        let restored = Connection::open_in_memory().expect("open");
        restored.deserialize(c"main", image).expect("deserialize");

        // RESIZEABLE is what makes this insert possible rather than SQLITE_FULL.
        let mut insert =
            Statement::prepare(&restored, "INSERT INTO example VALUES (8)").expect("compile");
        while insert.step().expect("step") == Step::Row {}
        insert.finalize().expect("finalize");
        assert_eq!(restored.changes(), 1);

        let mut count =
            Statement::prepare(&restored, "SELECT count(*) FROM example").expect("compile");
        assert_eq!(count.step().expect("step"), Step::Row);
        assert_eq!(count.column(0), ValueRef::Integer(2));
    }

    #[test]
    fn a_rejected_image_is_freed_rather_than_leaked() {
        let connection = Connection::open_in_memory().expect("open");
        let image = crate::SqlBytes::copy_from_slice(b"not a database at all").expect("allocate");
        // No schema by this name, so `sqlite3_deserialize` fails before it
        // installs the buffer -- and frees it itself, because `FREEONCLOSE`
        // already gave it ownership. That is why `deserialize` takes the image
        // by value and why nothing here has anything left to free. Running this
        // under a sanitizer is the real assertion.
        let error = connection
            .deserialize(c"nosuchschema", image)
            .expect_err("unknown schema");
        assert!(!error.code().is_ok());
    }

    #[test]
    fn a_corrupt_image_is_reported_when_it_is_read() {
        let connection = Connection::open_in_memory().expect("open");
        let image = crate::SqlBytes::copy_from_slice(b"not a database at all").expect("allocate");
        // `sqlite3_deserialize` installs the buffer without inspecting it; the
        // corruption surfaces on the first read, as SQLITE_NOTADB.
        connection.deserialize(c"main", image).expect("install");
        let error = connection
            .prepare_prefix("SELECT count(*) FROM sqlite_schema")
            .expect_err("read a corrupt image");
        assert_eq!(error.code().primary(), ResultCode::new(26));
    }
}
