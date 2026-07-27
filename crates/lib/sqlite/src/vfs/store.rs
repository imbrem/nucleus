//! A [`Vfs`] backed by a [`FileStore`] — a name-to-file mapping.
//!
//! [`FileStore`] is the minimal abstraction needed to turn a key/value
//! store into a full [`Vfs`]: it resolves path names to file handles.
//! [`StoreVfs`] wraps any `FileStore` into a [`Vfs`] implementation,
//! handling the protocol details (`OpenKind`, `OpenFlags`, `AccessCheck`,
//! etc.) so that stores only deal with names and files.
//!
//! # Provided implementations
//!
//! - [`HashMap<String, F>`] is a read-only store: it clones file handles
//!   on each open.  Pair it with [`ReadOnlyFile`](super::ReadOnlyFile) or
//!   `Arc<F>` for cheap clones.
//!
//! - [`Arc<F>`](std::sync::Arc) delegates all [`File`] methods to the
//!   inner `F`, making shared ownership trivial.  A mutable store can
//!   hold `Arc<F>` values and hand out clones to multiple connections.

use std::collections::HashMap;
use std::io;
use std::sync::Arc;

use super::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, SyncFlags, Vfs,
};

// ---------------------------------------------------------------------------
// FileStore trait
// ---------------------------------------------------------------------------

/// Maps names to file handles.
///
/// This is the core abstraction: any type that can look up a name and
/// return a [`File`] handle can be wrapped in [`StoreVfs`] to become a
/// full [`Vfs`].
///
/// The default [`delete`](FileStore::delete) and
/// [`writable`](FileStore::writable) implementations treat the store as
/// read-only. Override both to support mutable file sets.
pub trait FileStore: Send + Sync {
    /// The file handle type returned by [`open`](FileStore::open).
    type File: File;

    /// Returns a file handle for `name`.
    ///
    /// # Errors
    ///
    /// Returns [`io::ErrorKind::NotFound`] if no file with that name
    /// exists, or another error if the lookup fails.
    fn open(&self, name: &str) -> io::Result<Self::File>;

    /// Deletes the file named `name`.
    ///
    /// The default implementation returns
    /// [`io::ErrorKind::PermissionDenied`].
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be deleted.
    fn delete(&self, name: &str) -> io::Result<()> {
        let _ = name;
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only store",
        ))
    }

    /// Returns `true` if a file named `name` exists.
    fn exists(&self, name: &str) -> bool;

    /// Whether this store supports modifications (inserts and deletes).
    ///
    /// Used by [`StoreVfs`] to answer [`AccessCheck::ReadWrite`] queries.
    /// The default is `false`.
    fn writable(&self) -> bool {
        false
    }
}

// ---------------------------------------------------------------------------
// StoreVfs
// ---------------------------------------------------------------------------

/// A [`Vfs`] backed by a [`FileStore`].
///
/// Translates the `SQLite` VFS protocol into simple name-based lookups
/// on the underlying store. Path resolution is identity (names pass
/// through unchanged).
pub struct StoreVfs<S> {
    store: S,
}

impl<S: std::fmt::Debug> std::fmt::Debug for StoreVfs<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StoreVfs")
            .field("store", &self.store)
            .finish()
    }
}

impl<S> StoreVfs<S> {
    /// Wraps `store` as a VFS.
    #[must_use]
    pub fn new(store: S) -> Self {
        Self { store }
    }

    /// Returns a reference to the underlying store.
    #[must_use]
    pub fn store(&self) -> &S {
        &self.store
    }
}

impl<S: FileStore> Vfs for StoreVfs<S> {
    type File = S::File;

    fn open(
        &self,
        path: Option<&str>,
        _kind: OpenKind,
        _flags: OpenFlags,
    ) -> io::Result<Self::File> {
        let path = path.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "path required for store-backed VFS",
            )
        })?;
        self.store.open(path)
    }

    fn delete(&self, path: &str, _sync_dir: bool) -> io::Result<()> {
        self.store.delete(path)
    }

    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool> {
        match check {
            AccessCheck::Exists | AccessCheck::Read => Ok(self.store.exists(path)),
            AccessCheck::ReadWrite => Ok(self.store.writable() && self.store.exists(path)),
        }
    }

    fn full_pathname(&self, path: &str) -> io::Result<String> {
        Ok(path.to_owned())
    }
}

// ---------------------------------------------------------------------------
// HashMap as an immutable FileStore
// ---------------------------------------------------------------------------

impl<F: File + Clone, S: std::hash::BuildHasher + Send + Sync> FileStore for HashMap<String, F, S> {
    type File = F;

    fn open(&self, name: &str) -> io::Result<F> {
        self.get(name)
            .cloned()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, name.to_owned()))
    }

    fn exists(&self, name: &str) -> bool {
        self.contains_key(name)
    }
}

// ---------------------------------------------------------------------------
// Arc<F> as a File (delegation)
// ---------------------------------------------------------------------------

impl<F: File> File for Arc<F> {
    fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<()> {
        (**self).read(buf, offset)
    }

    fn write(&self, buf: &[u8], offset: u64) -> io::Result<()> {
        (**self).write(buf, offset)
    }

    fn truncate(&self, size: u64) -> io::Result<()> {
        (**self).truncate(size)
    }

    fn sync(&self, flags: SyncFlags) -> io::Result<()> {
        (**self).sync(flags)
    }

    fn file_size(&self) -> io::Result<u64> {
        (**self).file_size()
    }

    fn lock(&self, level: LockLevel) -> io::Result<()> {
        (**self).lock(level)
    }

    fn unlock(&self, level: LockLevel) -> io::Result<()> {
        (**self).unlock(level)
    }

    fn current_lock(&self) -> LockLevel {
        (**self).current_lock()
    }

    fn reserved(&self) -> bool {
        (**self).reserved()
    }

    fn sector_size(&self) -> usize {
        (**self).sector_size()
    }

    fn device_characteristics(&self) -> DeviceCharacteristics {
        (**self).device_characteristics()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vfs::ReadOnlyFile;

    fn make_store() -> HashMap<String, ReadOnlyFile<Arc<[u8]>>> {
        let mut m = HashMap::new();
        m.insert(
            "test.db".into(),
            ReadOnlyFile::new(Arc::from(b"hello world" as &[u8])),
        );
        m.insert(
            "empty.db".into(),
            ReadOnlyFile::new(Arc::from(b"" as &[u8])),
        );
        m
    }

    #[test]
    fn store_vfs_open_read() {
        let vfs = StoreVfs::new(make_store());
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        let mut buf = [0u8; 5];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"hello");
        assert_eq!(file.file_size().unwrap(), 11);
    }

    #[test]
    fn store_vfs_not_found() {
        let vfs = StoreVfs::new(make_store());
        let err = vfs
            .open(Some("missing.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn store_vfs_no_path() {
        let vfs = StoreVfs::new(make_store());
        let err = vfs
            .open(None, OpenKind::Temp, OpenFlags::DELETE_ON_CLOSE)
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }

    #[test]
    fn store_vfs_delete_denied() {
        let vfs = StoreVfs::new(make_store());
        let err = vfs.delete("test.db", false).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn store_vfs_access() {
        let vfs = StoreVfs::new(make_store());
        assert!(vfs.access("test.db", AccessCheck::Exists).unwrap());
        assert!(vfs.access("test.db", AccessCheck::Read).unwrap());
        assert!(!vfs.access("test.db", AccessCheck::ReadWrite).unwrap());
        assert!(!vfs.access("missing.db", AccessCheck::Exists).unwrap());
    }

    #[test]
    fn store_vfs_full_pathname() {
        let vfs = StoreVfs::new(make_store());
        assert_eq!(vfs.full_pathname("test.db").unwrap(), "test.db");
    }

    #[test]
    fn arc_file_delegation() {
        let inner = ReadOnlyFile::new(Arc::from(b"data" as &[u8]));
        let shared: Arc<ReadOnlyFile<Arc<[u8]>>> = Arc::new(inner);

        assert_eq!(shared.file_size().unwrap(), 4);
        let mut buf = [0u8; 4];
        shared.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"data");

        let err = shared.write(b"x", 0).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);

        assert_eq!(shared.current_lock(), LockLevel::None);
        assert!(!shared.reserved());
        assert_eq!(shared.sector_size(), 0);
        assert!(
            shared
                .device_characteristics()
                .contains(DeviceCharacteristics::IMMUTABLE)
        );
    }

    #[test]
    fn arc_file_in_hashmap_store() {
        let inner = ReadOnlyFile::new(Arc::from(b"shared" as &[u8]));
        let shared: Arc<ReadOnlyFile<Arc<[u8]>>> = Arc::new(inner);

        let mut files: HashMap<String, Arc<ReadOnlyFile<Arc<[u8]>>>> = HashMap::new();
        files.insert("a.db".into(), Arc::clone(&shared));
        files.insert("b.db".into(), Arc::clone(&shared));

        let vfs = StoreVfs::new(files);

        let a = vfs
            .open(Some("a.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        let b = vfs
            .open(Some("b.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        assert_eq!(a.file_size().unwrap(), 6);
        assert_eq!(b.file_size().unwrap(), 6);

        let mut buf = [0u8; 6];
        a.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"shared");
    }

    #[test]
    fn store_accessor() {
        let vfs = StoreVfs::new(make_store());
        assert!(vfs.store().contains_key("test.db"));
        assert!(!vfs.store().contains_key("missing.db"));
    }
}
