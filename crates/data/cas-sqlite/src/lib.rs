//! A small persistent CAS backed by `SQLite`.
//!
//! [`SqliteCas`] implements the ordinary [`Cas`] and [`CasShared`] provider
//! boundary. Nothing about it is trusted: raw reads remain bytes, and callers
//! obtain a [`CasFact`] only through the usual whole-object hash check. This
//! makes the store usable directly, behind an async adapter, or as one member
//! of a composed CAS without giving `SQLite` authority in the kernel.
//!
//! The schema is deliberately private and minimal. It stores one complete
//! object per 32-byte BLAKE3 address. Range-proof outboards and indexing are
//! separate policies and can be added without changing this table.

use std::ffi::CStr;
use std::ops::Range;
use std::sync::Arc;

use covalence_data_cas::{AsyncCas, AsyncCasError, Bytes, Cas, CasFuture, CasShared};
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, Statement, Step, ValueRef};

const ASYNC_READ_QUEUE_CAPACITY: usize = 32;
const SCHEMA: &str = "
CREATE TABLE IF NOT EXISTS cov_cas (
    addr BLOB PRIMARY KEY NOT NULL CHECK(length(addr) = 32),
    bytes BLOB NOT NULL
) WITHOUT ROWID;
";

/// Failure to open or use a [`SqliteCas`].
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The database could not be opened.
    #[snafu(display("could not open SQLite CAS: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: covalence_lib_sqlite::Error,
    },
    /// The CAS schema could not be initialized.
    #[snafu(display("could not initialize SQLite CAS schema: {source}"))]
    Schema {
        /// Underlying `SQLite` error.
        source: covalence_lib_sqlite::Error,
    },
    /// The background worker for asynchronous reads could not be started.
    #[snafu(display("could not start SQLite CAS async worker: {source}"))]
    WorkerStart {
        /// Underlying thread creation error.
        source: std::io::Error,
    },
    /// The background worker for asynchronous reads stopped unexpectedly.
    #[snafu(display("SQLite CAS async worker stopped"))]
    WorkerStopped,
    /// The bounded asynchronous read queue is full.
    #[snafu(display("SQLite CAS async read queue is full"))]
    WorkerBusy,
    /// An object lookup failed.
    #[snafu(display("could not read SQLite CAS object {address}: {source}"))]
    Read {
        /// Requested address.
        address: O256,
        /// Underlying `SQLite` error.
        source: covalence_lib_sqlite::Error,
    },
    /// An object could not be written.
    #[snafu(display("could not write SQLite CAS object {address}: {source}"))]
    Write {
        /// Object address.
        address: O256,
        /// Underlying `SQLite` error.
        source: covalence_lib_sqlite::Error,
    },
    /// Stored data used a type other than a `SQLite` blob.
    #[snafu(display("SQLite CAS object {address} is not stored as a blob"))]
    InvalidStorage {
        /// Requested address.
        address: O256,
    },
    /// A byte range was invalid for the stored object.
    #[snafu(display(
        "range {start}..{end} lies outside SQLite CAS object {address} of length {len}"
    ))]
    InvalidRange {
        /// Requested address.
        address: O256,
        /// Inclusive range start.
        start: u64,
        /// Exclusive range end.
        end: u64,
        /// Stored byte length.
        len: u64,
    },
}

/// A persistent whole-object CAS stored in one `SQLite` connection.
pub struct SqliteCas {
    connection: Arc<Connection>,
    async_reads: Option<std::sync::mpsc::SyncSender<ReadRequest>>,
    worker: Option<std::thread::JoinHandle<()>>,
}

struct ReadRequest {
    address: O256,
    reply: futures::channel::oneshot::Sender<Result<Option<Bytes>, Error>>,
}

impl SqliteCas {
    /// Opens or creates a database at `path` and initializes the CAS schema.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Open`] when the database cannot be opened, or
    /// [`Error::Schema`] when the CAS table cannot be initialized.
    pub fn open(path: &CStr) -> Result<Self, Error> {
        let connection = Connection::open(path).context(OpenSnafu)?;
        Self::from_connection(connection)
    }

    /// Creates a CAS in a private in-memory database.
    ///
    /// # Errors
    ///
    /// Returns an error when the database or schema cannot be initialized.
    pub fn open_in_memory() -> Result<Self, Error> {
        let connection = Connection::open_in_memory().context(OpenSnafu)?;
        Self::from_connection(connection)
    }

    /// Initializes a CAS in an existing connection.
    ///
    /// This does not take ownership of the database schema beyond the
    /// `cov_cas` table.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Schema`] when the table cannot be initialized, or
    /// [`Error::WorkerStart`] when the asynchronous reader cannot start.
    pub fn from_connection(connection: Connection) -> Result<Self, Error> {
        Statement::execute_batch(&connection, SCHEMA).context(SchemaSnafu)?;
        let connection = Arc::new(connection);
        let (async_reads, requests) =
            std::sync::mpsc::sync_channel::<ReadRequest>(ASYNC_READ_QUEUE_CAPACITY);
        let worker_connection = Arc::clone(&connection);
        let worker = std::thread::Builder::new()
            .name("sqlite-cas-reader".into())
            .spawn(move || {
                for request in requests {
                    if request.reply.is_canceled() {
                        continue;
                    }
                    let result = Self::read_connection(&worker_connection, request.address);
                    let _ = request.reply.send(result);
                }
            })
            .context(WorkerStartSnafu)?;
        Ok(Self {
            connection,
            async_reads: Some(async_reads),
            worker: Some(worker),
        })
    }

    fn read_connection(connection: &Connection, address: O256) -> Result<Option<Bytes>, Error> {
        let mut statement =
            Statement::prepare(connection, "SELECT bytes FROM cov_cas WHERE addr = ?1")
                .context(ReadSnafu { address })?;
        statement
            .bind_blob(1, address.as_ref())
            .context(ReadSnafu { address })?;
        match statement.step().context(ReadSnafu { address })? {
            Step::Done => Ok(None),
            Step::Row => match statement.column(0) {
                ValueRef::Blob(bytes) => Ok(Some(Bytes::copy_from_slice(bytes))),
                _ => InvalidStorageSnafu { address }.fail(),
            },
        }
    }

    fn read(&self, address: O256) -> Result<Option<Bytes>, Error> {
        Self::read_connection(&self.connection, address)
    }
}

impl Cas for SqliteCas {
    type Error = Error;

    fn get_bytes(&self, address: O256) -> Result<Option<Bytes>, Self::Error> {
        self.read(address)
    }

    fn get_range(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        let Some(bytes) = self.read(address)? else {
            return Ok(None);
        };
        let len = u64::try_from(bytes.len()).expect("CAS object length fits in u64");
        if range.start > range.end || range.end > len {
            return InvalidRangeSnafu {
                address,
                start: range.start,
                end: range.end,
                len,
            }
            .fail();
        }
        let start = usize::try_from(range.start).expect("validated range start fits in usize");
        let end = usize::try_from(range.end).expect("validated range end fits in usize");
        Ok(Some(bytes.slice(start..end)))
    }
}

impl CasShared for SqliteCas {
    type InsertSuccess = O256;
    type InsertError = Error;

    fn insert(&self, bytes: Bytes) -> Result<Self::InsertSuccess, Self::InsertError> {
        let address = O256::from_bytes(&bytes);
        let mut statement = Statement::prepare(
            &self.connection,
            "INSERT INTO cov_cas(addr, bytes) VALUES (?1, ?2) \
             ON CONFLICT(addr) DO UPDATE SET bytes = excluded.bytes",
        )
        .context(WriteSnafu { address })?;
        statement
            .bind_blob(1, address.as_ref())
            .context(WriteSnafu { address })?;
        statement
            .bind_blob(2, &bytes)
            .context(WriteSnafu { address })?;
        let step = statement.step().context(WriteSnafu { address })?;
        debug_assert_eq!(step, Step::Done);
        Ok(address)
    }
}

impl AsyncCas for SqliteCas {
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>> {
        let requests = self
            .async_reads
            .as_ref()
            .expect("SQLite CAS worker exists before drop")
            .clone();
        Box::pin(async move {
            let (sender, receiver) = futures::channel::oneshot::channel();
            match requests.try_send(ReadRequest {
                address,
                reply: sender,
            }) {
                Ok(()) => {}
                Err(std::sync::mpsc::TrySendError::Full(_)) => {
                    return Err(AsyncCasError::provider(Error::WorkerBusy));
                }
                Err(std::sync::mpsc::TrySendError::Disconnected(_)) => {
                    return Err(AsyncCasError::provider(Error::WorkerStopped));
                }
            }
            receiver
                .await
                .map_err(|_| AsyncCasError::provider(Error::WorkerStopped))?
                .map_err(AsyncCasError::provider)
        })
    }
}

impl Drop for SqliteCas {
    fn drop(&mut self) {
        self.async_reads.take();
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CString;

    use covalence_data_cas::{Cas, CasShared};
    use covalence_lib_hash::O256;
    use covalence_lib_sqlite::{Connection, Statement, Step, ValueRef};
    use covalence_logic_cas::CasExt;

    use super::{Error, SqliteCas};

    #[test]
    fn inserts_reads_ranges_and_reports_absence() {
        let cas = SqliteCas::open_in_memory().expect("open CAS");
        let missing = O256::from_bytes(b"missing");
        assert!(cas.get_bytes(missing).expect("read missing").is_none());

        let address = cas.insert("stored bytes".into()).expect("insert");
        assert_eq!(
            cas.get_bytes(address).expect("read").as_deref(),
            Some(b"stored bytes".as_slice())
        );
        assert_eq!(
            cas.get_range(address, 7..12)
                .expect("read range")
                .as_deref(),
            Some(b"bytes".as_slice())
        );
        assert!(matches!(
            cas.get_range(address, 0..13),
            Err(Error::InvalidRange { .. })
        ));
    }

    #[test]
    fn insertion_is_idempotent_and_checked_lookup_succeeds() {
        let cas = SqliteCas::open_in_memory().expect("open CAS");
        let first = cas.insert("same".into()).expect("first insert");
        let second = cas.insert("same".into()).expect("second insert");
        assert_eq!(first, second);
        let fact = cas
            .get_checked(first)
            .expect("checked read")
            .expect("present");
        assert_eq!(fact.hash(), first);
        assert_eq!(fact.as_ref(), b"same");
    }

    #[test]
    fn async_lookup_uses_the_background_reader() {
        let cas = SqliteCas::open_in_memory().expect("open CAS");
        let address = cas.insert("asynchronous".into()).expect("insert");
        let bytes =
            futures::executor::block_on(covalence_data_cas::AsyncCas::get_bytes(&cas, address))
                .expect("async read")
                .expect("present");
        assert_eq!(bytes, "asynchronous");
    }

    #[test]
    fn objects_persist_across_connections() {
        let path = std::env::temp_dir().join(format!(
            "covalence-cas-sqlite-{}-{}.sqlite",
            std::process::id(),
            O256::from_bytes(b"persistence test")
        ));
        let path = CString::new(path.to_string_lossy().as_bytes()).expect("path");
        let address = {
            let cas = SqliteCas::open(&path).expect("open first");
            cas.insert("persistent".into()).expect("insert")
        };
        let cas = SqliteCas::open(&path).expect("reopen");
        assert_eq!(
            cas.get_bytes(address).expect("read").as_deref(),
            Some(b"persistent".as_slice())
        );
        std::fs::remove_file(path.to_str().expect("UTF-8 path")).expect("remove database");
    }

    #[test]
    fn corruption_stays_untrusted_and_checked_lookup_rejects_it() {
        let connection = Connection::open_in_memory().expect("open database");
        let address = O256::from_bytes(b"expected");
        let cas = SqliteCas::from_connection(connection).expect("initialize CAS");

        let mut statement = Statement::prepare(
            &cas.connection,
            "INSERT INTO cov_cas(addr, bytes) VALUES (?1, ?2)",
        )
        .expect("prepare corruption");
        statement
            .bind_blob(1, address.as_ref())
            .expect("bind address");
        statement.bind_blob(2, b"wrong").expect("bind wrong bytes");
        statement.step().expect("insert corruption");

        assert_eq!(
            cas.get_bytes(address).expect("raw read").as_deref(),
            Some(b"wrong".as_slice())
        );
        assert!(cas.get_checked(address).is_err());
    }

    #[test]
    fn insertion_repairs_a_corrupt_row() {
        let connection = Connection::open_in_memory().expect("open database");
        let address = O256::from_bytes(b"expected");
        let cas = SqliteCas::from_connection(connection).expect("initialize CAS");
        let mut statement = Statement::prepare(
            &cas.connection,
            "INSERT INTO cov_cas(addr, bytes) VALUES (?1, ?2)",
        )
        .expect("prepare corruption");
        statement
            .bind_blob(1, address.as_ref())
            .expect("bind address");
        statement.bind_blob(2, b"wrong").expect("bind wrong bytes");
        statement.step().expect("insert corruption");

        assert_eq!(cas.insert("expected".into()).expect("repair"), address);
        assert!(cas.get_checked(address).expect("check repaired").is_some());
    }

    #[test]
    fn schema_is_one_without_rowid_cov_cas_table() {
        let cas = SqliteCas::open_in_memory().expect("open CAS");
        let mut schema = Statement::prepare(
            &cas.connection,
            "SELECT name, sql FROM sqlite_schema \
             WHERE type = 'table' AND name LIKE 'cov%cas%'",
        )
        .expect("inspect schema");
        assert_eq!(schema.step().expect("read table"), Step::Row);
        assert!(matches!(schema.column(0), ValueRef::Text(b"cov_cas")));
        let ValueRef::Text(sql) = schema.column(1) else {
            panic!("schema SQL is text");
        };
        let sql = std::str::from_utf8(sql).expect("schema SQL is UTF-8");
        assert!(sql.contains("addr BLOB PRIMARY KEY"));
        assert!(sql.contains("bytes BLOB NOT NULL"));
        assert!(sql.ends_with("WITHOUT ROWID"));
        assert_eq!(schema.step().expect("finish schema query"), Step::Done);
    }
}
