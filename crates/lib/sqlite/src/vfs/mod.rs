//! Traits for implementing an `SQLite` virtual file system.
//!
//! This module defines a safe Rust API that mirrors the `SQLite` VFS layer
//! without exposing any C-level details. Implementors provide a [`Vfs`] and
//! its associated [`File`] type; the registration mechanism that wires these
//! traits into the `SQLite` C library is a separate concern (see e.g. the
//! `sqlite-plugin` crate).
//!
//! The trait surface is intentionally minimal: it covers the operations that
//! `SQLite` requires in order to open, read, write, and synchronise database
//! files. Advisory locking is included because `SQLite` calls these methods
//! even for single-connection in-process databases.

#[cfg(feature = "vfs-register")]
mod ffi;
mod readonly;
#[cfg(feature = "vfs-register")]
mod registry;

pub use readonly::{ReadOnlyFile, ReadOnlyVfs};
#[cfg(feature = "vfs-register")]
pub use registry::{RegisterError, VfsName, register};

use std::io;

/// The kind of file `SQLite` is opening.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpenKind {
    /// The main database file.
    MainDb,
    /// The rollback journal.
    Journal,
    /// The write-ahead log.
    Wal,
    /// A temporary, transient, subjournal, or super-journal file.
    ///
    /// These roles are intentionally collapsed in the first-pass API because
    /// the immutable VFS does not serve them. They can be separated without
    /// changing the FFI adapter's ownership model when an implementation
    /// needs role-specific behavior.
    Temp,
}

/// A file opened by a [`Vfs`], together with the access mode actually granted.
#[derive(Debug)]
pub struct OpenedFile<F> {
    /// Open file handle.
    pub file: F,
    /// Actual open flags. These may be narrower than those requested.
    pub flags: OpenFlags,
}

impl<F> OpenedFile<F> {
    /// Creates an open result with its actual access flags.
    #[must_use]
    pub fn new(file: F, flags: OpenFlags) -> Self {
        Self { file, flags }
    }
}

impl<F> std::ops::Deref for OpenedFile<F> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        &self.file
    }
}

bitflags::bitflags! {
    /// Modifier flags passed alongside [`OpenKind`] when opening a file.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct OpenFlags: u32 {
        /// The file should be created if it does not exist.
        const CREATE           = 1 << 0;
        /// The file should be opened for exclusive access.
        const EXCLUSIVE        = 1 << 1;
        /// The file should be opened read-only.
        const READ_ONLY        = 1 << 2;
        /// The file should be deleted when closed.
        const DELETE_ON_CLOSE  = 1 << 3;
        /// The file should be opened for reads and writes.
        const READ_WRITE       = 1 << 4;
    }
}

/// The kind of access being checked in [`Vfs::access`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccessCheck {
    /// Check whether the file exists.
    Exists,
    /// Check whether the file can be read.
    Read,
    /// Check whether the file can be read and written.
    ReadWrite,
}

/// The synchronisation level requested by `SQLite`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SyncFlags {
    /// Ordinary sync — ensure data is on stable storage.
    Normal,
    /// Full sync — ensure both data and metadata are durable.
    Full,
    /// Data-only sync — skip file metadata.
    DataOnly,
}

/// The advisory lock level held on a database file.
///
/// `SQLite` uses a five-state locking model. Transitions always move through
/// adjacent states except for the jump from `Shared` to `Exclusive` via
/// `Reserved` and `Pending`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LockLevel {
    /// No lock held.
    None,
    /// A shared (read) lock.
    Shared,
    /// A reserved lock — only one connection may hold this at a time,
    /// but existing shared locks are allowed to continue.
    Reserved,
    /// A pending lock — no new shared locks may be acquired, but
    /// existing ones may finish.
    Pending,
    /// An exclusive (write) lock.
    Exclusive,
}

bitflags::bitflags! {
    /// Device characteristics reported by a file.
    ///
    /// These hints tell `SQLite` how to optimise I/O for the underlying
    /// storage.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct DeviceCharacteristics: u32 {
        /// Writes of any size are atomic — no partial pages.
        const ATOMIC              = 1 << 0;
        /// Writes aligned to 512-byte boundaries are atomic.
        const ATOMIC_512          = 1 << 1;
        /// Writes aligned to 1024-byte boundaries are atomic.
        const ATOMIC_1K           = 1 << 2;
        /// Writes aligned to 2048-byte boundaries are atomic.
        const ATOMIC_2K           = 1 << 3;
        /// Writes aligned to 4096-byte boundaries are atomic.
        const ATOMIC_4K           = 1 << 4;
        /// Writes aligned to 8192-byte boundaries are atomic.
        const ATOMIC_8K           = 1 << 5;
        /// Writes aligned to 16384-byte boundaries are atomic.
        const ATOMIC_16K          = 1 << 6;
        /// Writes aligned to 32768-byte boundaries are atomic.
        const ATOMIC_32K          = 1 << 7;
        /// Writes aligned to 65536-byte boundaries are atomic.
        const ATOMIC_64K          = 1 << 8;
        /// An `fsync` is safe to use in place of separate data and metadata
        /// syncs.
        const SAFE_APPEND         = 1 << 9;
        /// The file is on sequential-access storage.
        const SEQUENTIAL          = 1 << 10;
        /// The file cannot be deleted while open.
        const UNDELETABLE_WHEN_OPEN =
            crate::ffi::SQLITE_IOCAP_UNDELETABLE_WHEN_OPEN as u32;
        /// The file does not need to be synced.
        const POWERSAFE_OVERWRITE =
            crate::ffi::SQLITE_IOCAP_POWERSAFE_OVERWRITE as u32;
        /// The file is immutable — it will never change.
        const IMMUTABLE = crate::ffi::SQLITE_IOCAP_IMMUTABLE as u32;
        /// The storage layer batches writes and syncs them together.
        const BATCH_ATOMIC = crate::ffi::SQLITE_IOCAP_BATCH_ATOMIC as u32;
    }
}

/// A virtual file system for `SQLite`.
///
/// Implementors define how database files are created, opened, and located.
/// Each `Vfs` has an associated [`File`] type that handles I/O on individual
/// open files.
pub trait Vfs {
    /// The file handle type returned by [`open`](Vfs::open).
    type File: File;

    /// Opens or creates a file.
    ///
    /// `path` is `None` when `SQLite` requests a temporary file whose name
    /// the VFS may choose freely. `kind` describes the role of the file
    /// (main database, journal, WAL, or temporary).
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be opened under the given flags.
    fn open(
        &self,
        path: Option<&str>,
        kind: OpenKind,
        flags: OpenFlags,
    ) -> io::Result<OpenedFile<Self::File>>;

    /// Deletes the file at `path`.
    ///
    /// If `sync_dir` is true, the directory containing the file should be
    /// synced after the deletion to ensure the removal is durable.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be removed.
    fn delete(&self, path: &str, sync_dir: bool) -> io::Result<()>;

    /// Checks whether `path` satisfies `check`.
    ///
    /// # Errors
    ///
    /// Returns an error if the check itself cannot be performed. Returning
    /// `Ok(false)` means the check was performed but the condition is not
    /// met.
    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool>;

    /// Resolves `path` to a full, canonical pathname.
    ///
    /// # Errors
    ///
    /// Returns an error if the path cannot be resolved.
    fn full_pathname(&self, path: &str) -> io::Result<String>;
}

/// An open file within a [`Vfs`].
///
/// This trait covers the I/O methods that `SQLite` calls on an open database
/// file, journal, or WAL. Implementations must handle reads, writes, and
/// advisory locking.
///
/// All methods take `&self` because `SQLite` may call file methods from
/// multiple threads. Implementations should use interior mutability (e.g.
/// `Mutex`) for any mutable state.
pub trait File: Send + Sync {
    /// Reads bytes starting at `offset`, returning the initialized byte count.
    ///
    /// A short read returns a count smaller than `buf.len()`. The FFI adapter
    /// zero-fills the remainder and reports `SQLITE_IOERR_SHORT_READ`.
    ///
    /// # Errors
    ///
    /// Returns an error if the read fails for a reason other than a short
    /// file.
    fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<usize>;

    /// Writes `buf` starting at `offset`.
    ///
    /// # Errors
    ///
    /// Returns an error if the write cannot be completed.
    fn write(&self, buf: &[u8], offset: u64) -> io::Result<()>;

    /// Truncates the file to `size` bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be truncated.
    fn truncate(&self, size: u64) -> io::Result<()>;

    /// Syncs the file contents (and optionally metadata) to stable storage.
    ///
    /// # Errors
    ///
    /// Returns an error if the sync fails.
    fn sync(&self, flags: SyncFlags) -> io::Result<()>;

    /// Returns the current size of the file in bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the size cannot be determined.
    fn file_size(&self) -> io::Result<u64>;

    /// Attempts to acquire a lock at the given level.
    ///
    /// # Errors
    ///
    /// Returns an error if the lock cannot be acquired.
    fn lock(&self, level: LockLevel) -> io::Result<()>;

    /// Releases the lock to the given level.
    ///
    /// # Errors
    ///
    /// Returns an error if the lock cannot be released.
    fn unlock(&self, level: LockLevel) -> io::Result<()>;

    /// Returns the current lock level.
    fn current_lock(&self) -> LockLevel;

    /// Returns whether any connection holds a reserved lock.
    ///
    /// The default returns `true` when this file's own lock is at least
    /// [`LockLevel::Reserved`].
    fn reserved(&self) -> bool {
        self.current_lock() >= LockLevel::Reserved
    }

    /// Returns the sector size of the underlying storage in bytes.
    ///
    /// `SQLite` uses this to align I/O. A return value of 0 lets `SQLite`
    /// choose a default (typically 4096).
    fn sector_size(&self) -> usize {
        0
    }

    /// Reports the device characteristics of the underlying storage.
    fn device_characteristics(&self) -> DeviceCharacteristics {
        DeviceCharacteristics::empty()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;

    struct MemVfs;

    struct MemFile {
        data: Mutex<Vec<u8>>,
        lock: Mutex<LockLevel>,
    }

    impl Vfs for MemVfs {
        type File = MemFile;

        fn open(
            &self,
            _path: Option<&str>,
            _kind: OpenKind,
            flags: OpenFlags,
        ) -> io::Result<OpenedFile<Self::File>> {
            Ok(OpenedFile::new(
                MemFile {
                    data: Mutex::new(Vec::new()),
                    lock: Mutex::new(LockLevel::None),
                },
                flags,
            ))
        }

        fn delete(&self, _path: &str, _sync_dir: bool) -> io::Result<()> {
            Ok(())
        }

        fn access(&self, _path: &str, _check: AccessCheck) -> io::Result<bool> {
            Ok(false)
        }

        fn full_pathname(&self, path: &str) -> io::Result<String> {
            Ok(path.to_owned())
        }
    }

    impl File for MemFile {
        fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<usize> {
            let data = self.data.lock().unwrap();
            let offset = usize::try_from(offset).unwrap_or(usize::MAX);
            let available = data.len().saturating_sub(offset);
            let to_copy = buf.len().min(available);
            if to_copy > 0 {
                buf[..to_copy].copy_from_slice(&data[offset..offset + to_copy]);
            }
            buf[to_copy..].fill(0);
            Ok(to_copy)
        }

        fn write(&self, buf: &[u8], offset: u64) -> io::Result<()> {
            let mut data = self.data.lock().unwrap();
            let offset = usize::try_from(offset)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "offset too large"))?;
            let end = offset + buf.len();
            if end > data.len() {
                data.resize(end, 0);
            }
            data[offset..end].copy_from_slice(buf);
            Ok(())
        }

        fn truncate(&self, size: u64) -> io::Result<()> {
            let size = usize::try_from(size)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "size too large"))?;
            self.data.lock().unwrap().truncate(size);
            Ok(())
        }

        fn sync(&self, _flags: SyncFlags) -> io::Result<()> {
            Ok(())
        }

        fn file_size(&self) -> io::Result<u64> {
            Ok(self.data.lock().unwrap().len() as u64)
        }

        fn lock(&self, level: LockLevel) -> io::Result<()> {
            *self.lock.lock().unwrap() = level;
            Ok(())
        }

        fn unlock(&self, level: LockLevel) -> io::Result<()> {
            *self.lock.lock().unwrap() = level;
            Ok(())
        }

        fn current_lock(&self) -> LockLevel {
            *self.lock.lock().unwrap()
        }
    }

    #[test]
    fn mem_vfs_round_trip() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        file.file.write(b"hello", 0).unwrap();
        assert_eq!(file.file.file_size().unwrap(), 5);

        let mut buf = [0u8; 5];
        file.file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"hello");
    }

    #[test]
    fn short_read_zero_fills() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        file.write(b"ab", 0).unwrap();
        let mut buf = [0xffu8; 4];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, &[b'a', b'b', 0, 0]);
    }

    #[test]
    fn read_beyond_eof_fills_zeros() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        let mut buf = [0xffu8; 4];
        file.read(&mut buf, 100).unwrap();
        assert_eq!(&buf, &[0, 0, 0, 0]);
    }

    #[test]
    fn write_at_offset_extends_file() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        file.write(b"world", 10).unwrap();
        assert_eq!(file.file_size().unwrap(), 15);

        let mut buf = [0u8; 15];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf[..10], &[0u8; 10]);
        assert_eq!(&buf[10..], b"world");
    }

    #[test]
    fn truncate_shrinks_file() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        file.write(b"hello world", 0).unwrap();
        file.truncate(5).unwrap();
        assert_eq!(file.file_size().unwrap(), 5);

        let mut buf = [0u8; 5];
        file.read(&mut buf, 0).unwrap();
        assert_eq!(&buf, b"hello");
    }

    #[test]
    fn lock_transitions() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        assert_eq!(file.current_lock(), LockLevel::None);
        file.lock(LockLevel::Shared).unwrap();
        assert_eq!(file.current_lock(), LockLevel::Shared);
        file.lock(LockLevel::Exclusive).unwrap();
        assert_eq!(file.current_lock(), LockLevel::Exclusive);
        file.unlock(LockLevel::None).unwrap();
        assert_eq!(file.current_lock(), LockLevel::None);
    }

    #[test]
    fn lock_level_ordering() {
        assert!(LockLevel::None < LockLevel::Shared);
        assert!(LockLevel::Shared < LockLevel::Reserved);
        assert!(LockLevel::Reserved < LockLevel::Pending);
        assert!(LockLevel::Pending < LockLevel::Exclusive);
    }

    #[test]
    fn default_sector_size_is_zero() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();
        assert_eq!(file.sector_size(), 0);
    }

    #[test]
    fn default_device_characteristics_are_empty() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();
        let chars = file.device_characteristics();
        assert_eq!(chars, DeviceCharacteristics::empty());
    }

    #[test]
    fn reserved_lock_check() {
        let vfs = MemVfs;
        let file = vfs
            .open(None, OpenKind::MainDb, OpenFlags::default())
            .unwrap();

        assert!(!file.reserved());
        file.lock(LockLevel::Shared).unwrap();
        assert!(!file.reserved());
        file.lock(LockLevel::Reserved).unwrap();
        assert!(file.reserved());
        file.lock(LockLevel::Exclusive).unwrap();
        assert!(file.reserved());
    }

    #[test]
    fn access_check_variants() {
        let vfs = MemVfs;
        assert!(!vfs.access("/nonexistent", AccessCheck::Exists).unwrap());
        assert!(!vfs.access("/nonexistent", AccessCheck::Read).unwrap());
        assert!(!vfs.access("/nonexistent", AccessCheck::ReadWrite).unwrap());
    }

    #[test]
    fn full_pathname_returns_input() {
        let vfs = MemVfs;
        assert_eq!(vfs.full_pathname("test.db").unwrap(), "test.db");
    }

    #[test]
    fn open_flags_composition() {
        let flags = OpenFlags::CREATE | OpenFlags::EXCLUSIVE;
        assert!(flags.contains(OpenFlags::CREATE));
        assert!(flags.contains(OpenFlags::EXCLUSIVE));
        assert!(!flags.contains(OpenFlags::READ_ONLY));
    }

    #[test]
    fn device_characteristics_composition() {
        let chars = DeviceCharacteristics::ATOMIC | DeviceCharacteristics::IMMUTABLE;
        assert!(chars.contains(DeviceCharacteristics::ATOMIC));
        assert!(chars.contains(DeviceCharacteristics::IMMUTABLE));
        assert!(!chars.contains(DeviceCharacteristics::SEQUENTIAL));
    }

    #[test]
    fn device_characteristics_match_sqlite_abi() {
        assert_eq!(
            DeviceCharacteristics::UNDELETABLE_WHEN_OPEN.bits(),
            crate::ffi::SQLITE_IOCAP_UNDELETABLE_WHEN_OPEN as u32
        );
        assert_eq!(
            DeviceCharacteristics::POWERSAFE_OVERWRITE.bits(),
            crate::ffi::SQLITE_IOCAP_POWERSAFE_OVERWRITE as u32
        );
        assert_eq!(
            DeviceCharacteristics::IMMUTABLE.bits(),
            crate::ffi::SQLITE_IOCAP_IMMUTABLE as u32
        );
        assert_eq!(
            DeviceCharacteristics::BATCH_ATOMIC.bits(),
            crate::ffi::SQLITE_IOCAP_BATCH_ATOMIC as u32
        );
    }

    #[test]
    fn open_kind_distinguishes_file_roles() {
        let vfs = MemVfs;
        let _main = vfs
            .open(Some("test.db"), OpenKind::MainDb, OpenFlags::CREATE)
            .unwrap();
        let _journal = vfs
            .open(
                Some("test.db-journal"),
                OpenKind::Journal,
                OpenFlags::CREATE,
            )
            .unwrap();
        let _wal = vfs
            .open(Some("test.db-wal"), OpenKind::Wal, OpenFlags::CREATE)
            .unwrap();
        let _temp = vfs
            .open(None, OpenKind::Temp, OpenFlags::DELETE_ON_CLOSE)
            .unwrap();
    }
}
