#![allow(unsafe_code)]
//! Process-global registry for Rust [`Vfs`] implementations.

use std::ffi::{CStr, CString, c_int, c_void};
use std::fmt;
use std::num::NonZeroUsize;
use std::ptr;
use std::sync::{LazyLock, Mutex};

use covalence_lib_error::snafu::Snafu;
use indexmap::IndexMap;

use super::{Vfs, ffi};

/// A validated name used to select an `SQLite` VFS.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct VfsName {
    text: String,
    ffi: CString,
}

impl VfsName {
    /// Validates an `SQLite` VFS name.
    ///
    /// # Errors
    ///
    /// Returns [`RegisterError::InvalidName`] when `name` is empty or
    /// contains an interior NUL byte.
    pub fn new(name: &str) -> Result<Self, RegisterError> {
        if name.is_empty() {
            return Err(RegisterError::InvalidName);
        }
        let ffi = CString::new(name).map_err(|_| RegisterError::InvalidName)?;
        Ok(Self {
            text: name.to_owned(),
            ffi,
        })
    }

    /// Returns the name as UTF-8 text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.text
    }

    /// Returns the name in the form `SQLite` takes it.
    ///
    /// This is the same bytes as [`as_str`](Self::as_str), NUL-terminated. It
    /// exists so selecting a VFS -- `Connection::open_with_flags` -- needs no
    /// allocation and no fallible conversion: validation already happened.
    #[must_use]
    pub fn as_c_str(&self) -> &CStr {
        &self.ffi
    }
}

impl AsRef<str> for VfsName {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Display for VfsName {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// Opaque process-local identity of a registered `SQLite` VFS.
///
/// Equality compares the actual `sqlite3_vfs` pointers. Names select VFSes;
/// this value identifies the implementation `SQLite` registered and later
/// used.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct VfsIdentity(NonZeroUsize);

impl fmt::Debug for VfsIdentity {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("VfsIdentity(..)")
    }
}

impl VfsIdentity {
    fn from_pointer(pointer: *mut crate::ffi::sqlite3_vfs) -> Option<Self> {
        NonZeroUsize::new(pointer.addr()).map(Self)
    }
}

/// A VFS registered in this process, including its selector and identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegisteredVfs {
    name: VfsName,
    identity: VfsIdentity,
}

impl RegisteredVfs {
    /// Returns the generated or caller-supplied `SQLite` VFS name.
    #[must_use]
    pub const fn name(&self) -> &VfsName {
        &self.name
    }

    /// Returns the actual process-local identity registered with `SQLite`.
    #[must_use]
    pub const fn identity(&self) -> VfsIdentity {
        self.identity
    }
}

/// Failure to obtain the VFS used by an attached database.
#[derive(Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum VfsIdentityError {
    /// The `SQLite` database name contains an interior NUL byte.
    #[snafu(display("invalid SQLite database name"))]
    InvalidDatabaseName,
    /// `sqlite3_file_control` returned a non-OK result code.
    #[snafu(display("sqlite3_file_control failed with code {code}"))]
    FileControlFailed {
        /// The result code `SQLite` returned.
        code: c_int,
    },
    /// `SQLite` returned success without setting the VFS pointer.
    #[snafu(display("SQLite returned a null VFS pointer"))]
    MissingPointer,
}

/// Errors returned by [`register`].
#[derive(Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RegisterError {
    /// The VFS name is empty or contains an interior NUL byte.
    #[snafu(display("invalid VFS name"))]
    InvalidName,
    /// A VFS with this name is already registered with `SQLite`.
    #[snafu(display("a VFS with this name is already registered"))]
    AlreadyRegistered,
    /// The process-local unique-name space has been exhausted.
    #[snafu(display("the process-local VFS name space is exhausted"))]
    NameSpaceExhausted,
    /// `sqlite3_vfs_register` returned a non-OK result code.
    #[snafu(display("sqlite3_vfs_register failed with code {code}"))]
    RegistrationFailed {
        /// The result code `SQLite` returned.
        code: c_int,
    },
}

/// Registry of VFS instances installed in `SQLite`'s process-global list.
struct Registry {
    entries: IndexMap<VfsName, VfsIdentity>,
    next_unique: u64,
}

impl Default for Registry {
    fn default() -> Self {
        Self {
            entries: IndexMap::new(),
            next_unique: 1,
        }
    }
}

impl Registry {
    fn unique_name(&mut self) -> Result<VfsName, RegisterError> {
        loop {
            let id = self.next_unique;
            self.next_unique = id.checked_add(1).ok_or(RegisterError::NameSpaceExhausted)?;
            let name = VfsName::new(&format!("covalence-{id:016x}"))?;
            if !self.entries.contains_key(&name) && !ffi::name_exists(&name.ffi) {
                return Ok(name);
            }
        }
    }

    fn register<V: Vfs + Send + Sync + 'static>(
        &mut self,
        name: VfsName,
        vfs: V,
        as_default: bool,
    ) -> Result<RegisteredVfs, RegisterError> {
        if self.entries.contains_key(&name) {
            return Err(RegisterError::AlreadyRegistered);
        }

        // The registry mutex serializes this lookup with calls to our public
        // register function. An external SQLite user can still register a
        // name, so SQLite remains authoritative.
        if ffi::name_exists(&name.ffi) {
            return Err(RegisterError::AlreadyRegistered);
        }

        let pointer = ffi::register(name.ffi.clone(), vfs, as_default)
            .map_err(|code| RegisterError::RegistrationFailed { code })?;
        let Some(identity) = VfsIdentity::from_pointer(pointer) else {
            unreachable!("Box::into_raw returned a null VFS pointer");
        };
        self.entries.insert(name.clone(), identity);
        Ok(RegisteredVfs { name, identity })
    }
}

static REGISTRY: LazyLock<Mutex<Registry>> = LazyLock::new(|| Mutex::new(Registry::default()));

/// Registers a [`Vfs`] implementation with `SQLite`.
///
/// The returned [`RegisteredVfs`] contains both the name used to select the VFS
/// and the pointer identity needed to verify what `SQLite` actually opened.
/// Reusing a registered name is an error even when both instances have the
/// same concrete Rust type.
///
/// Registered VFS state intentionally lives for the process lifetime because
/// `SQLite` exposes VFS registration as global state.
/// Foreign registration may race for a name, but cannot invalidate the
/// leaked adapter; callers can verify the VFS through [`VfsIdentity`].
///
/// # Errors
///
/// Returns an error for an invalid or conflicting name, or when `SQLite`
/// rejects the registration.
pub fn register<V: Vfs + Send + Sync + 'static>(
    name: &str,
    vfs: V,
    as_default: bool,
) -> Result<RegisteredVfs, RegisterError> {
    let name = VfsName::new(name)?;
    REGISTRY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .register(name, vfs, as_default)
}

/// Registers a [`Vfs`] under a fresh process-local name.
///
/// The VFS is never installed as `SQLite`'s default. Its generated name can be
/// supplied explicitly to connection-opening APIs or in an `SQLite` file URI.
/// Registered VFS state lives for the remainder of the process.
///
/// A name is only a selector. Security-sensitive callers must query the actual
/// post-open pointer with [`ConnectionVfsExt::database_vfs`] and compare it to
/// [`RegisteredVfs::identity`].
///
/// # Errors
///
/// Returns an error if the unique-name space is exhausted or `SQLite` rejects
/// the registration.
pub fn register_unique<V: Vfs + Send + Sync + 'static>(
    vfs: V,
) -> Result<RegisteredVfs, RegisterError> {
    let mut registry = REGISTRY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let name = registry.unique_name()?;
    registry.register(name, vfs, false)
}

/// VFS identity inspection for an `SQLite` connection.
pub trait ConnectionVfsExt {
    /// Returns the actual VFS pointer used by an attached database.
    ///
    /// `database` is an `SQLite` schema name such as `main` or the name passed
    /// to `ATTACH`. The result comes from `SQLITE_FCNTL_VFS_POINTER`; it is not
    /// inferred from a URI or VFS name.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` rejects the file control or returns a null
    /// pointer.
    fn database_vfs(&self, database: &CStr) -> Result<VfsIdentity, VfsIdentityError>;
}

impl ConnectionVfsExt for crate::Connection {
    fn database_vfs(&self, database: &CStr) -> Result<VfsIdentity, VfsIdentityError> {
        let mut pointer = ptr::null_mut::<crate::ffi::sqlite3_vfs>();
        // SAFETY: `self.as_ptr()` is used only for the duration of this call;
        // `database` is NUL-terminated; and the fourth argument points to the
        // writable `sqlite3_vfs*` slot required by SQLITE_FCNTL_VFS_POINTER.
        let result = unsafe {
            crate::ffi::sqlite3_file_control(
                self.as_ptr(),
                database.as_ptr(),
                crate::ffi::SQLITE_FCNTL_VFS_POINTER,
                ptr::from_mut(&mut pointer).cast::<c_void>(),
            )
        };
        if result != crate::ffi::SQLITE_OK {
            return Err(VfsIdentityError::FileControlFailed { code: result });
        }
        VfsIdentity::from_pointer(pointer).ok_or(VfsIdentityError::MissingPointer)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    use crate::{Connection, OpenFlags, Statement, Step};

    use super::*;
    use crate::vfs::ReadOnlyVfs;

    static NEXT_NAME: AtomicU64 = AtomicU64::new(0);

    /// Runs a statement expected to return one integer.
    fn scalar(connection: &Connection, sql: &str) -> i64 {
        let mut statement = Statement::prepare(connection, sql).expect("compile");
        assert_eq!(statement.step().unwrap(), Step::Row);
        statement.column(0).as_integer().unwrap()
    }

    fn unique_name() -> String {
        format!(
            "covalence-test-{}",
            NEXT_NAME.fetch_add(1, Ordering::Relaxed)
        )
    }

    #[test]
    fn vfs_name_rejects_empty_and_nul() {
        assert_eq!(VfsName::new("").unwrap_err(), RegisterError::InvalidName);
        assert_eq!(
            VfsName::new("bad\0name").unwrap_err(),
            RegisterError::InvalidName
        );
    }

    #[test]
    fn vfs_name_preserves_visible_name() {
        let name = VfsName::new("repository-42").unwrap();
        assert_eq!(name.as_str(), "repository-42");
        assert_eq!(name.to_string(), "repository-42");
    }

    #[test]
    fn registered_read_only_vfs_opens_database() {
        let temporary = std::env::temp_dir();
        std::fs::create_dir_all(&temporary).unwrap();
        let path = temporary.join(format!("{}.sqlite", unique_name()));
        {
            let path = CString::new(path.to_str().unwrap()).unwrap();
            let connection = Connection::open(&path).unwrap();
            Statement::execute_batch(
                &connection,
                "CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);",
            )
            .expect("populate");
        }
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();

        let logical_path = "repository/database.sqlite";
        let files = HashMap::from([(
            logical_path.to_owned(),
            Arc::<[u8]>::from(bytes.into_boxed_slice()),
        )]);
        let registered = register(&unique_name(), ReadOnlyVfs::new(files), false).unwrap();

        let path = CString::new(logical_path).unwrap();
        let connection = Connection::open_with_flags(
            &path,
            OpenFlags::READ_ONLY,
            Some(registered.name().as_c_str()),
        )
        .unwrap();
        assert_eq!(
            connection.database_vfs(c"main").unwrap(),
            registered.identity()
        );
        assert_eq!(scalar(&connection, "SELECT n FROM value"), 42);
    }

    #[test]
    fn registered_names_identify_instances() {
        let name = unique_name();
        register(&name, ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new()), false).unwrap();
        assert_eq!(
            register(&name, ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new()), false).unwrap_err(),
            RegisterError::AlreadyRegistered
        );
    }

    #[test]
    fn unique_registration_generates_distinct_names() {
        let first = register_unique(ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new())).unwrap();
        let second = register_unique(ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new())).unwrap();

        assert_ne!(first, second);
        assert!(first.name().as_str().starts_with("covalence-"));
        assert!(second.name().as_str().starts_with("covalence-"));
    }

    #[test]
    fn uniquely_registered_vfs_supports_immutable_attach() {
        let temporary = std::env::temp_dir();
        std::fs::create_dir_all(&temporary).unwrap();
        let path = temporary.join(format!("{}.sqlite", unique_name()));
        {
            let path = CString::new(path.to_str().unwrap()).unwrap();
            let connection = Connection::open(&path).unwrap();
            Statement::execute_batch(
                &connection,
                "CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);",
            )
            .expect("populate");
        }
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();

        let logical_path = "immutable.sqlite";
        let files = HashMap::from([(
            logical_path.to_owned(),
            Arc::<[u8]>::from(bytes.into_boxed_slice()),
        )]);
        let registered = register_unique(ReadOnlyVfs::new(files)).unwrap();
        let uri = format!(
            "file:{logical_path}?mode=ro&immutable=1&vfs={}",
            registered.name().as_str()
        );
        let connection = Connection::open_in_memory().unwrap();
        {
            let mut statement =
                Statement::prepare(&connection, "ATTACH DATABASE ?1 AS imported").expect("compile");
            statement.bind_text(1, &uri).unwrap();
            statement.step().unwrap();
        }

        assert_eq!(
            connection.database_vfs(c"imported").unwrap(),
            registered.identity()
        );
        assert_ne!(
            connection.database_vfs(c"main").unwrap(),
            registered.identity()
        );

        assert_eq!(scalar(&connection, "SELECT n FROM imported.value"), 42);
        // Immutable means immutable: the write is refused rather than applied
        // to a copy no one would ever see again.
        let mut insert = Statement::prepare(&connection, "INSERT INTO imported.value VALUES (7)")
            .expect("compile");
        assert!(insert.step().is_err());
    }
}
