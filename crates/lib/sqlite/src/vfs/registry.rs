#![allow(unsafe_code)]
//! Process-global registry for Rust [`Vfs`] implementations.

use std::ffi::{CString, c_int};
use std::fmt;
use std::sync::{LazyLock, Mutex};

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

/// Errors returned by [`register`].
#[derive(Debug, Eq, PartialEq)]
pub enum RegisterError {
    /// The VFS name is empty or contains an interior NUL byte.
    InvalidName,
    /// A VFS with this name is already registered with `SQLite`.
    AlreadyRegistered,
    /// `sqlite3_vfs_register` returned a non-OK result code.
    RegistrationFailed(c_int),
}

impl fmt::Display for RegisterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidName => formatter.write_str("invalid VFS name"),
            Self::AlreadyRegistered => {
                formatter.write_str("a VFS with this name is already registered")
            }
            Self::RegistrationFailed(code) => {
                write!(formatter, "sqlite3_vfs_register failed with code {code}")
            }
        }
    }
}

impl std::error::Error for RegisterError {}

/// Registry of VFS instances installed in `SQLite`'s process-global list.
#[derive(Default)]
struct Registry {
    entries: IndexMap<VfsName, ()>,
}

impl Registry {
    fn register<V: Vfs + Send + Sync + 'static>(
        &mut self,
        name: VfsName,
        vfs: V,
        as_default: bool,
    ) -> Result<VfsName, RegisterError> {
        if self.entries.contains_key(&name) {
            return Err(RegisterError::AlreadyRegistered);
        }

        // The registry mutex serializes this lookup with calls to our public
        // register function. An external SQLite user can still register a
        // name, so SQLite remains authoritative.
        if ffi::name_exists(&name.ffi) {
            return Err(RegisterError::AlreadyRegistered);
        }

        ffi::register(name.ffi.clone(), vfs, as_default)
            .map_err(RegisterError::RegistrationFailed)?;
        self.entries.insert(name.clone(), ());
        Ok(name)
    }
}

static REGISTRY: LazyLock<Mutex<Registry>> = LazyLock::new(|| Mutex::new(Registry::default()));

/// Registers a [`Vfs`] implementation with `SQLite`.
///
/// The returned [`VfsName`] can be retained as metadata and passed to
/// connection-opening APIs. Names identify instances, so reusing a registered
/// name is an error even when both instances have the same concrete Rust type.
///
/// Registered VFS state intentionally lives for the process lifetime because
/// `SQLite` exposes VFS registration as global state.
///
/// # Safety
///
/// The caller must ensure that no code outside this registry concurrently
/// registers or unregisters an `SQLite` VFS with the same name. `SQLite`'s
/// process-global registry does not provide an atomic reserve-by-name
/// operation, so the check performed here cannot make that external race
/// safe.
///
/// # Errors
///
/// Returns an error for an invalid or conflicting name, or when `SQLite`
/// rejects the registration.
pub unsafe fn register<V: Vfs + Send + Sync + 'static>(
    name: &str,
    vfs: V,
    as_default: bool,
) -> Result<VfsName, RegisterError> {
    let name = VfsName::new(name)?;
    REGISTRY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .register(name, vfs, as_default)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::io;
    use std::ops::Range;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    use crate::{Connection, OpenFlags as SqliteOpenFlags};

    use super::*;
    use bytes::Bytes;
    use covalence_data_cas::Cas;
    use covalence_lib_hash::{O256, Obj};

    use crate::vfs::{CasVfs, ReadOnlyVfs};

    static NEXT_NAME: AtomicU64 = AtomicU64::new(0);
    const CAS_ADDRESS: O256 = Obj::from_array([0x42; 32]);

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
        let path = std::env::temp_dir().join(format!("{}.sqlite", unique_name()));
        {
            let connection = Connection::open(&path).unwrap();
            connection
                .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
                .unwrap();
        }
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();

        let logical_path = "repository/database.sqlite";
        let files = HashMap::from([(
            logical_path.to_owned(),
            Arc::<[u8]>::from(bytes.into_boxed_slice()),
        )]);
        // SAFETY: test names are unique and no external code registers them.
        let name = unsafe { register(&unique_name(), ReadOnlyVfs::new(files), false) }.unwrap();

        let connection = Connection::open_with_flags_and_vfs(
            logical_path,
            SqliteOpenFlags::SQLITE_OPEN_READ_ONLY,
            name.as_str(),
        )
        .unwrap();
        assert_eq!(
            connection
                .query_row("SELECT n FROM value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );
    }

    struct MemoryCas(Bytes);

    impl Cas for MemoryCas {
        type Error = io::Error;

        fn len(&self, address: O256) -> io::Result<Option<u64>> {
            Ok((address == CAS_ADDRESS).then_some(self.0.len() as u64))
        }

        fn read(&self, address: O256, range: Range<u64>) -> io::Result<Option<Bytes>> {
            if address != CAS_ADDRESS {
                return Ok(None);
            }
            let start = usize::try_from(range.start)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            let end = usize::try_from(range.end)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            Ok(self.0.get(start..end).map(Bytes::copy_from_slice))
        }
    }

    #[test]
    fn registered_cas_vfs_queries_database_by_address() {
        let path = std::env::temp_dir().join(format!("{}.sqlite", unique_name()));
        {
            let connection = Connection::open(&path).unwrap();
            connection
                .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
                .unwrap();
        }
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        // SAFETY: test names are unique and no external code registers them.
        let name = unsafe {
            register(
                &unique_name(),
                CasVfs::new(Arc::new(MemoryCas(Bytes::from(bytes)))),
                false,
            )
        }
        .unwrap();

        let connection = Connection::open_with_flags_and_vfs(
            CAS_ADDRESS.to_string(),
            SqliteOpenFlags::SQLITE_OPEN_READ_ONLY,
            name.as_str(),
        )
        .unwrap();
        assert_eq!(
            connection
                .query_row("SELECT n FROM value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );
    }

    #[test]
    fn registered_names_identify_instances() {
        let name = unique_name();
        // SAFETY: this test exclusively owns its unique registration name.
        unsafe { register(&name, ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new()), false) }.unwrap();
        assert_eq!(
            // SAFETY: this is serialized with the first call and exercises
            // the registry's duplicate-name error.
            unsafe { register(&name, ReadOnlyVfs::<Arc<[u8]>>::new(HashMap::new()), false) }
                .unwrap_err(),
            RegisterError::AlreadyRegistered
        );
    }
}
