//! Read-only [`Vfs`] and [`File`] implementations backed by in-memory byte
//! buffers.
//!
//! [`ReadOnlyVfs`] maps path names to byte blobs and serves them as
//! immutable database files.  [`ReadOnlyFile`] wraps any `T: AsRef<[u8]>`
//! (e.g. `Vec<u8>`, `Arc<[u8]>`, `&'static [u8]`) and exposes it through
//! the [`File`] trait.
//!
//! This is a building block for content-addressed storage: a CAS VFS can
//! resolve paths to content hashes, fetch the corresponding blob, and hand
//! it back as a `ReadOnlyFile<Arc<[u8]>>`.

use std::collections::HashMap;
use std::io;

use super::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, SyncFlags, Vfs,
};

// ---------------------------------------------------------------------------
// ReadOnlyFile
// ---------------------------------------------------------------------------

/// A read-only [`File`] backed by a contiguous byte buffer.
///
/// `T` is any type whose bytes can be borrowed as `&[u8]` — for example
/// `Vec<u8>`, `Arc<[u8]>`, `&'static [u8]`, or `bytes::Bytes`.
///
/// Writes and truncations return [`io::ErrorKind::PermissionDenied`].
/// The file reports [`DeviceCharacteristics::IMMUTABLE`] so that `SQLite`
/// can skip change detection.
pub struct ReadOnlyFile<T> {
    data: T,
}

impl<T: std::fmt::Debug> std::fmt::Debug for ReadOnlyFile<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReadOnlyFile")
            .field("data", &self.data)
            .finish_non_exhaustive()
    }
}

impl<T> ReadOnlyFile<T> {
    /// Wraps `data` in a read-only file handle.
    #[must_use]
    pub fn new(data: T) -> Self {
        Self { data }
    }
}

impl<T: AsRef<[u8]> + Send + Sync> File for ReadOnlyFile<T> {
    fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<()> {
        let data = self.data.as_ref();
        #[allow(clippy::cast_possible_truncation)]
        let offset = offset as usize;
        let available = data.len().saturating_sub(offset);
        let to_copy = buf.len().min(available);
        if to_copy > 0 {
            buf[..to_copy].copy_from_slice(&data[offset..offset + to_copy]);
        }
        buf[to_copy..].fill(0);
        Ok(())
    }

    fn write(&self, _buf: &[u8], _offset: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only file",
        ))
    }

    fn truncate(&self, _size: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only file",
        ))
    }

    fn sync(&self, _flags: SyncFlags) -> io::Result<()> {
        Ok(())
    }

    fn file_size(&self) -> io::Result<u64> {
        Ok(self.data.as_ref().len() as u64)
    }

    fn lock(&self, _level: LockLevel) -> io::Result<()> {
        Ok(())
    }

    fn unlock(&self, _level: LockLevel) -> io::Result<()> {
        Ok(())
    }

    fn current_lock(&self) -> LockLevel {
        LockLevel::None
    }

    fn device_characteristics(&self) -> DeviceCharacteristics {
        DeviceCharacteristics::IMMUTABLE
    }
}

// ---------------------------------------------------------------------------
// ReadOnlyVfs
// ---------------------------------------------------------------------------

/// A read-only [`Vfs`] backed by a fixed set of named files.
///
/// Each entry maps a path to a byte buffer of type `T`.  When `SQLite`
/// opens a path, the corresponding buffer is cloned into a
/// [`ReadOnlyFile`].  For cheap clones, use `T = Arc<[u8]>`.
///
/// Deletions and writes are rejected with
/// [`io::ErrorKind::PermissionDenied`].
pub struct ReadOnlyVfs<T> {
    files: HashMap<String, T>,
}

impl<T> ReadOnlyVfs<T> {
    /// Creates a VFS from the given path-to-data mapping.
    #[must_use]
    pub fn new(files: HashMap<String, T>) -> Self {
        Self { files }
    }
}

impl<T: AsRef<[u8]> + Clone + Send + Sync> Vfs for ReadOnlyVfs<T> {
    type File = ReadOnlyFile<T>;

    fn open(
        &self,
        path: Option<&str>,
        _kind: OpenKind,
        _flags: OpenFlags,
    ) -> io::Result<Self::File> {
        let path = path.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "path required for read-only VFS",
            )
        })?;
        let data = self
            .files
            .get(path)
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, path.to_owned()))?
            .clone();
        Ok(ReadOnlyFile::new(data))
    }

    fn delete(&self, _path: &str, _sync_dir: bool) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only VFS",
        ))
    }

    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool> {
        match check {
            AccessCheck::Exists | AccessCheck::Read => Ok(self.files.contains_key(path)),
            AccessCheck::ReadWrite => Ok(false),
        }
    }

    fn full_pathname(&self, path: &str) -> io::Result<String> {
        Ok(path.to_owned())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn make_vfs() -> ReadOnlyVfs<Arc<[u8]>> {
        let mut files = HashMap::new();
        files.insert("test.db".into(), Arc::from(b"hello world" as &[u8]));
        files.insert("empty.db".into(), Arc::from(b"" as &[u8]));
        ReadOnlyVfs::new(files)
    }

    #[test]
    fn read_existing_file() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let mut buf = [0u8; 5];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"hello");
        assert_eq!(file.file_size().unwrap(), 11);
    }

    #[test]
    fn read_with_offset() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let mut buf = [0u8; 5];
        file.read(&mut buf, 6).unwrap();
        assert_eq!(&buf, b"world");
    }

    #[test]
    fn short_read_zero_fills() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let mut buf = [0xffu8; 4];
        file.read(&mut buf, 9).unwrap();
        assert_eq!(&buf, &[b'l', b'd', 0, 0]);
    }

    #[test]
    fn read_beyond_eof() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let mut buf = [0xffu8; 4];
        file.read(&mut buf, 100).unwrap();
        assert_eq!(&buf, &[0, 0, 0, 0]);
    }

    #[test]
    fn write_returns_permission_denied() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let err = file.write(b"x", 0).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn truncate_returns_permission_denied() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        let err = file.truncate(0).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn open_nonexistent_returns_not_found() {
        let vfs = make_vfs();
        let err = vfs
            .open(Some("missing.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn open_without_path_returns_error() {
        let vfs = make_vfs();
        let err = vfs
            .open(None, OpenKind::Temp, OpenFlags::DELETE_ON_CLOSE)
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }

    #[test]
    fn delete_returns_permission_denied() {
        let vfs = make_vfs();
        let err = vfs.delete("test.db", false).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn access_checks() {
        let vfs = make_vfs();
        assert!(vfs.access("test.db", AccessCheck::Exists).unwrap());
        assert!(vfs.access("test.db", AccessCheck::Read).unwrap());
        assert!(!vfs.access("test.db", AccessCheck::ReadWrite).unwrap());
        assert!(!vfs.access("missing.db", AccessCheck::Exists).unwrap());
    }

    #[test]
    fn reports_immutable() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        assert!(
            file.device_characteristics()
                .contains(DeviceCharacteristics::IMMUTABLE)
        );
    }

    #[test]
    fn sync_is_noop() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        file.sync(SyncFlags::Full).unwrap();
    }

    #[test]
    fn lock_is_noop() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        assert_eq!(file.current_lock(), LockLevel::None);
        file.lock(LockLevel::Shared).unwrap();
        assert_eq!(file.current_lock(), LockLevel::None);
        file.unlock(LockLevel::None).unwrap();
        assert_eq!(file.current_lock(), LockLevel::None);
    }

    #[test]
    fn empty_file() {
        let vfs = make_vfs();
        let file = vfs
            .open(Some("empty.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();

        assert_eq!(file.file_size().unwrap(), 0);
        let mut buf = [0xffu8; 2];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, &[0, 0]);
    }

    #[test]
    fn works_with_vec() {
        let mut files = HashMap::new();
        files.insert("a.db".into(), b"data".to_vec());
        let vfs = ReadOnlyVfs::new(files);
        let file = vfs
            .open(Some("a.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        assert_eq!(file.file_size().unwrap(), 4);
    }

    #[test]
    fn works_with_static_slice() {
        let mut files: HashMap<String, &'static [u8]> = HashMap::new();
        files.insert("a.db".into(), b"static");
        let vfs = ReadOnlyVfs::new(files);
        let file = vfs
            .open(Some("a.db"), OpenKind::MainDb, OpenFlags::READ_ONLY)
            .unwrap();
        assert_eq!(file.file_size().unwrap(), 6);
    }
}
