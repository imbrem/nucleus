//! A content-addressed `SQLite` REPL.
//!
//! The surface here is deliberately small. It does three things:
//!
//! 1. admits bytes into a content-addressed store and reports what it holds;
//! 2. owns raw `SQLite` connections, several at a time;
//! 3. opens the real `SQLite` shell with the store mounted.
//!
//! What it deliberately does **not** do is run SQL. There is no statement
//! surface here, no result formatting, and no dot-command vocabulary of our
//! own invention, because the third item already provides all of that and does
//! it better. Every previous attempt at this layer grew a second SQL shell;
//! this one refuses the job.
//!
//! # Trust
//!
//! Nothing in this crate is trusted. Connections are raw, the shell runs
//! arbitrary SQL, and store contents are uninterpreted bytes. What *is*
//! load-bearing is that these operations cannot corrupt anything: the store is
//! immutable and content-addressed, the mount is read-only, and dropping an
//! address cannot disturb an open database.

use std::sync::Arc;

use covalence_data_cas::{AdmissionError, CasStats, MemoryCas};
use covalence_lib_hash::O256;
use covalence_lib_sqlite::Connection;
use covalence_lib_sqlite::vfs::{
    CAS_VFS_NAME, ConnectionVfsExt, RegisterError, RegisteredVfs, VfsIdentity, VfsIdentityError,
    register_cas,
};

/// Handle for one raw connection owned by a [`Repl`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConnectionId(u64);

impl ConnectionId {
    /// Returns the numeric handle shown to the user.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }

    /// Reconstructs a handle from a number typed by the user.
    ///
    /// A handle that was never issued, or has been closed, is simply unknown
    /// to the [`Repl`], so this cannot manufacture access to anything.
    #[must_use]
    pub const fn from_raw(id: u64) -> Self {
        Self(id)
    }
}

impl std::fmt::Display for ConnectionId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

/// What a [`Repl`] can fail to do.
#[derive(Debug)]
pub enum ReplError {
    /// The content-addressed mount could not be registered with `SQLite`.
    Mount(RegisterError),
    /// Bytes exceeded the store's admission limit.
    Admission(AdmissionError),
    /// `SQLite` refused an operation.
    Sqlite(covalence_lib_sqlite::Error),
    /// No connection carries this handle.
    UnknownConnection(ConnectionId),
    /// An operation needing a selected connection ran with none selected.
    NoSelection,
    /// `SQLite` would not report which VFS backs a database.
    VfsIdentity(VfsIdentityError),
    /// `SQLite` opened a database through some VFS other than the mount.
    ///
    /// The URI named the mount, so this means the name was not honoured. It is
    /// reported rather than tolerated because a name is routing data and only
    /// the pointer is evidence.
    NotMounted,
}

impl std::fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mount(error) => write!(formatter, "could not mount the store: {error}"),
            Self::Admission(error) => write!(formatter, "{error}"),
            Self::Sqlite(error) => write!(formatter, "{error}"),
            Self::UnknownConnection(id) => write!(formatter, "no connection {id}"),
            Self::NoSelection => formatter.write_str("no connection is selected"),
            Self::VfsIdentity(error) => write!(formatter, "{error}"),
            Self::NotMounted => {
                formatter.write_str("database was not opened through the content-addressed mount")
            }
        }
    }
}

impl std::error::Error for ReplError {}

impl From<RegisterError> for ReplError {
    fn from(error: RegisterError) -> Self {
        Self::Mount(error)
    }
}

impl From<AdmissionError> for ReplError {
    fn from(error: AdmissionError) -> Self {
        Self::Admission(error)
    }
}

impl From<covalence_lib_sqlite::Error> for ReplError {
    fn from(error: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

impl From<VfsIdentityError> for ReplError {
    fn from(error: VfsIdentityError) -> Self {
        Self::VfsIdentity(error)
    }
}

/// One connection and the description under which it was opened.
#[derive(Debug)]
struct Entry {
    id: ConnectionId,
    origin: String,
    connection: Connection,
}

/// What a connection is and where it came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConnectionInfo {
    /// The connection's handle.
    pub id: ConnectionId,
    /// How it was opened — a URI, or a description of an anonymous database.
    pub origin: String,
    /// Whether it is the currently selected connection.
    pub selected: bool,
}

/// A content-addressed store, mounted, plus the connections over it.
pub struct Repl {
    cas: Arc<MemoryCas>,
    mount: RegisteredVfs,
    connections: Vec<Entry>,
    selected: Option<ConnectionId>,
    next_id: u64,
}

impl Repl {
    /// Creates a REPL whose store is mounted under `CAS_VFS_NAME`.
    ///
    /// The mount is process-global and permanent, so at most one `Repl` per
    /// process may use the conventional name. Use [`Self::with_mount_name`]
    /// for additional instances, and note that `?vfs=cas` will then only reach
    /// the first.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` rejects the registration, which includes
    /// the name already being taken.
    pub fn new() -> Result<Self, ReplError> {
        Self::with_mount_name(CAS_VFS_NAME, false)
    }

    /// Creates a REPL whose store is mounted under `name`.
    ///
    /// `as_default` installs the mount as `SQLite`'s default VFS. That makes a
    /// bare address openable, at the cost of requiring ordinary filesystem
    /// paths to name the platform VFS explicitly.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` rejects the registration.
    pub fn with_mount_name(name: &str, as_default: bool) -> Result<Self, ReplError> {
        let cas = Arc::new(MemoryCas::new());
        // SAFETY: `register_cas` inherits SQLite's process-global registration
        // contract. Nothing in this workspace registers VFS names outside the
        // one registry, and a concurrent external registration of this exact
        // name is reported as an error rather than silently accepted.
        #[allow(unsafe_code, reason = "mounts the store in SQLite's global registry")]
        let mount = unsafe { register_cas(Arc::clone(&cas), name, as_default) }?;
        Ok(Self {
            cas,
            mount,
            connections: Vec::new(),
            selected: None,
            next_id: 1,
        })
    }

    /// Borrows the content-addressed store.
    #[must_use]
    pub fn cas(&self) -> &Arc<MemoryCas> {
        &self.cas
    }

    /// Returns the registered mount, including its pointer identity.
    #[must_use]
    pub const fn mount(&self) -> &RegisteredVfs {
        &self.mount
    }

    /// Admits complete bytes and returns their address.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes exceed the store's admission limit.
    pub fn put(&self, bytes: impl Into<bytes::Bytes>) -> Result<O256, ReplError> {
        Ok(self.cas.insert(bytes)?)
    }

    /// Drops an address from the store, reporting whether it resolved.
    ///
    /// # Effect on open databases
    ///
    /// A database currently open through this address **will start failing its
    /// reads**. The mount resolves every page through the store rather than
    /// capturing the object at open, so removal is visible immediately.
    ///
    /// This is weaker than the intended semantics, under which an outstanding
    /// handle keeps its object resolvable and removal only affects future
    /// opens. It is safe — a failed read is an error, never wrong bytes — but
    /// it is not yet the contract. Delivering it needs the store to hand out
    /// pinned objects rather than answer address-keyed reads, which is a change
    /// to the `Cas` interface itself. Tracked in the foundation issue.
    #[must_use = "the return value says whether the address was resident"]
    pub fn forget(&self, address: O256) -> bool {
        self.cas.remove(address)
    }

    /// Summarises what the store holds.
    #[must_use]
    pub fn stats(&self) -> CasStats {
        self.cas.stats()
    }

    /// Returns every resolvable address.
    #[must_use]
    pub fn addresses(&self) -> Vec<O256> {
        self.cas.addresses()
    }

    /// Returns the `SQLite` URI which opens `address` through this mount.
    #[must_use]
    pub fn uri(&self, address: O256) -> String {
        format!(
            "file:{}?mode=ro&immutable=1&vfs={}",
            address.hex(),
            self.mount.name().as_str()
        )
    }

    /// Opens a private in-memory database and selects it.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot open the database.
    pub fn open_memory(&mut self) -> Result<ConnectionId, ReplError> {
        let connection = Connection::open_in_memory()?;
        Ok(self.insert(":memory:".to_owned(), connection))
    }

    /// Opens `uri` and selects the resulting connection.
    ///
    /// A `?vfs=` parameter naming this REPL's mount reaches the store.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot open the URI.
    pub fn open_uri(&mut self, uri: &str) -> Result<ConnectionId, ReplError> {
        use covalence_lib_sqlite::OpenFlags;

        let connection = Connection::open_with_flags(
            uri,
            OpenFlags::SQLITE_OPEN_READ_WRITE
                | OpenFlags::SQLITE_OPEN_CREATE
                | OpenFlags::SQLITE_OPEN_URI,
        )?;
        Ok(self.insert(uri.to_owned(), connection))
    }

    /// Opens the object at `address` read-only through the mount.
    ///
    /// # Errors
    ///
    /// Returns an error if the address does not resolve, if `SQLite` cannot
    /// open it, or if the database `SQLite` actually opened did not come from
    /// this mount.
    pub fn open_address(&mut self, address: O256) -> Result<ConnectionId, ReplError> {
        use covalence_lib_sqlite::OpenFlags;

        let uri = self.uri(address);
        let connection = Connection::open_with_flags(
            &uri,
            OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_URI,
        )?;

        // The URI asked for this mount. This is the check that it got it.
        if connection.database_vfs("main")? != self.mount.identity() {
            return Err(ReplError::NotMounted);
        }

        Ok(self.insert(uri, connection))
    }

    /// Returns the identity of the VFS backing a connection's schema.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown handle or when `SQLite` will not report
    /// the pointer.
    pub fn database_vfs(&self, id: ConnectionId, schema: &str) -> Result<VfsIdentity, ReplError> {
        Ok(self.get(id)?.connection.database_vfs(schema)?)
    }

    /// Lists every open connection.
    #[must_use]
    pub fn connections(&self) -> Vec<ConnectionInfo> {
        self.connections
            .iter()
            .map(|entry| ConnectionInfo {
                id: entry.id,
                origin: entry.origin.clone(),
                selected: self.selected == Some(entry.id),
            })
            .collect()
    }

    /// Returns the selected connection's handle, if any.
    #[must_use]
    pub const fn selected(&self) -> Option<ConnectionId> {
        self.selected
    }

    /// Selects an existing connection.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection carries this handle.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), ReplError> {
        self.get(id)?;
        self.selected = Some(id);
        Ok(())
    }

    /// Borrows a connection for direct `SQLite` use.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection carries this handle.
    pub fn connection(&self, id: ConnectionId) -> Result<&Connection, ReplError> {
        Ok(&self.get(id)?.connection)
    }

    /// Borrows the selected connection.
    ///
    /// # Errors
    ///
    /// Returns an error if nothing is selected.
    pub fn selected_connection(&self) -> Result<&Connection, ReplError> {
        self.connection(self.selected.ok_or(ReplError::NoSelection)?)
    }

    /// Closes a connection, clearing the selection if it was selected.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection carries this handle.
    pub fn close(&mut self, id: ConnectionId) -> Result<(), ReplError> {
        let index = self
            .connections
            .iter()
            .position(|entry| entry.id == id)
            .ok_or(ReplError::UnknownConnection(id))?;
        self.connections.remove(index);
        if self.selected == Some(id) {
            self.selected = self.connections.last().map(|entry| entry.id);
        }
        Ok(())
    }

    fn insert(&mut self, origin: String, connection: Connection) -> ConnectionId {
        let id = ConnectionId(self.next_id);
        self.next_id += 1;
        self.connections.push(Entry {
            id,
            origin,
            connection,
        });
        self.selected = Some(id);
        id
    }

    fn get(&self, id: ConnectionId) -> Result<&Entry, ReplError> {
        self.connections
            .iter()
            .find(|entry| entry.id == id)
            .ok_or(ReplError::UnknownConnection(id))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    static NEXT: AtomicU64 = AtomicU64::new(0);

    /// Each test needs its own mount: registration is process-global and
    /// permanent, so the conventional name can only be taken once.
    fn repl() -> Repl {
        let name = format!(
            "covalence-test-repl-{}",
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        Repl::with_mount_name(&name, false).unwrap()
    }

    fn database_image() -> Vec<u8> {
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
            .unwrap();
        connection
            .serialize(covalence_lib_sqlite::MAIN_DB)
            .unwrap()
            .to_vec()
    }

    #[test]
    fn admitted_bytes_open_as_a_database() {
        let mut repl = repl();
        let address = repl.put(database_image()).unwrap();
        let id = repl.open_address(address).unwrap();

        assert_eq!(
            repl.connection(id)
                .unwrap()
                .query_row("SELECT n FROM value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );
    }

    #[test]
    fn an_opened_address_actually_came_from_the_mount() {
        let mut repl = repl();
        let address = repl.put(database_image()).unwrap();
        let id = repl.open_address(address).unwrap();
        assert_eq!(
            repl.database_vfs(id, "main").unwrap(),
            repl.mount().identity()
        );
    }

    #[test]
    fn the_mount_is_read_only() {
        let mut repl = repl();
        let address = repl.put(database_image()).unwrap();
        let id = repl.open_address(address).unwrap();
        assert!(
            repl.connection(id)
                .unwrap()
                .execute("INSERT INTO value VALUES (7)", [])
                .is_err()
        );
    }

    /// Pins down the *current* removal semantics, which are weaker than
    /// intended. When the store learns to hand out pinned objects this test
    /// should invert: the open connection must keep answering.
    #[test]
    fn forgetting_an_address_currently_breaks_open_databases() {
        let mut repl = repl();
        let address = repl.put(database_image()).unwrap();
        let id = repl.open_address(address).unwrap();

        assert!(repl.forget(address));

        // Reads fail, because the mount re-resolves each page through the
        // store. They fail cleanly: an I/O error, never wrong bytes.
        assert!(
            repl.connection(id)
                .unwrap()
                .query_row("SELECT n FROM value", [], |row| row.get::<_, i64>(0))
                .is_err()
        );
        // A fresh open fails too.
        assert!(repl.open_address(address).is_err());
    }

    #[test]
    fn several_connections_coexist_and_are_independently_closable() {
        let mut repl = repl();
        let first = repl.open_memory().unwrap();
        let second = repl.open_memory().unwrap();
        assert_ne!(first, second);
        assert_eq!(repl.selected(), Some(second));

        repl.connection(first)
            .unwrap()
            .execute_batch("CREATE TABLE only_in_first (n INTEGER)")
            .unwrap();
        // Separate databases: the table is not visible from the other.
        assert!(
            repl.connection(second)
                .unwrap()
                .query_row("SELECT count(*) FROM only_in_first", [], |row| row
                    .get::<_, i64>(0))
                .is_err()
        );

        repl.select(first).unwrap();
        assert_eq!(repl.selected(), Some(first));

        repl.close(first).unwrap();
        assert!(repl.connection(first).is_err());
        assert_eq!(repl.selected(), Some(second));
        assert_eq!(repl.connections().len(), 1);
    }

    #[test]
    fn closing_an_unknown_connection_is_an_error() {
        let mut repl = repl();
        assert!(matches!(
            repl.close(ConnectionId(99)),
            Err(ReplError::UnknownConnection(_))
        ));
    }

    #[test]
    fn the_store_reports_what_it_holds() {
        let repl = repl();
        assert_eq!(repl.stats(), CasStats::default());
        let address = repl.put(&b"hello"[..]).unwrap();
        assert_eq!(repl.stats().objects, 1);
        assert_eq!(repl.stats().bytes, 5);
        assert_eq!(repl.addresses(), vec![address]);
    }

    #[test]
    fn an_unresolvable_address_does_not_open() {
        let mut repl = repl();
        assert!(
            repl.open_address(O256::from_bytes(b"never admitted"))
                .is_err()
        );
    }
}
