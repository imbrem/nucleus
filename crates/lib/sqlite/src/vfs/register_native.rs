//! Registration adapter for native targets using the `sqlite-vfs` crate.
//!
//! Bridges our [`Vfs`](super::Vfs) / [`File`](super::File) traits to
//! [`sqlite_vfs::Vfs`] / [`sqlite_vfs::DatabaseHandle`] and delegates to
//! [`sqlite_vfs::register`] for the actual FFI registration.

use std::borrow::Cow;
use std::io;
use std::ops::Range;
use std::time::Duration;

use super::{AccessCheck, File, LockLevel, OpenFlags, OpenKind, SyncFlags, Vfs};

// ---------------------------------------------------------------------------
// VFS adapter
// ---------------------------------------------------------------------------

/// Wraps a [`Vfs`] to implement [`sqlite_vfs::Vfs`].
struct VfsAdapter<V>(V);

impl<V> sqlite_vfs::Vfs for VfsAdapter<V>
where
    V: Vfs + Sync,
    V::File: Sync,
{
    type Handle = FileAdapter<V::File>;

    fn open(
        &self,
        db: &str,
        opts: sqlite_vfs::OpenOptions,
    ) -> Result<Self::Handle, io::Error> {
        let kind = to_our_open_kind(opts.kind);
        let flags = to_our_open_flags(opts.access);
        let file = self.0.open(Some(db), kind, flags)?;
        Ok(FileAdapter(file))
    }

    fn delete(&self, db: &str) -> Result<(), io::Error> {
        self.0.delete(db, false)
    }

    fn exists(&self, db: &str) -> Result<bool, io::Error> {
        self.0.access(db, AccessCheck::Exists)
    }

    fn temporary_name(&self) -> String {
        use std::fmt::Write as _;
        let mut buf = [0u8; 16];
        rand::fill(&mut buf);
        let hex = buf
            .iter()
            .fold(String::with_capacity(32), |mut s, b| {
                let _ = write!(s, "{b:02x}");
                s
            });
        format!("/tmp/sqlite_{hex}")
    }

    fn random(&self, buffer: &mut [i8]) {
        // `rand` generates `u8`; reinterpret each byte as `i8` (same bit
        // pattern, intentional wrap).
        for b in buffer.iter_mut() {
            *b = rand::random::<u8>().cast_signed();
        }
    }

    fn sleep(&self, duration: Duration) -> Duration {
        std::thread::sleep(duration);
        duration
    }

    fn access(&self, db: &str, write: bool) -> Result<bool, io::Error> {
        let check = if write {
            AccessCheck::ReadWrite
        } else {
            AccessCheck::Read
        };
        self.0.access(db, check)
    }

    fn full_pathname<'a>(&self, db: &'a str) -> Result<Cow<'a, str>, io::Error> {
        self.0.full_pathname(db).map(Cow::Owned)
    }
}

// ---------------------------------------------------------------------------
// File (DatabaseHandle) adapter
// ---------------------------------------------------------------------------

/// Wraps a [`File`] to implement [`sqlite_vfs::DatabaseHandle`].
struct FileAdapter<F>(F);

impl<F: File + Sync> sqlite_vfs::DatabaseHandle for FileAdapter<F> {
    type WalIndex = WalIndexStub;

    fn size(&self) -> Result<u64, io::Error> {
        self.0.file_size()
    }

    fn read_exact_at(&mut self, buf: &mut [u8], offset: u64) -> Result<(), io::Error> {
        // Our `File::read` zero-fills short reads and returns `Ok(())`.
        // `sqlite_vfs` expects `Err(UnexpectedEof)` for short reads.
        let file_len = self.0.file_size()?;
        self.0.read(buf, offset)?;
        if offset + buf.len() as u64 > file_len {
            Err(io::Error::new(io::ErrorKind::UnexpectedEof, "short read"))
        } else {
            Ok(())
        }
    }

    fn write_all_at(&mut self, buf: &[u8], offset: u64) -> Result<(), io::Error> {
        self.0.write(buf, offset)
    }

    fn sync(&mut self, data_only: bool) -> Result<(), io::Error> {
        let flags = if data_only {
            SyncFlags::DataOnly
        } else {
            SyncFlags::Normal
        };
        self.0.sync(flags)
    }

    fn set_len(&mut self, size: u64) -> Result<(), io::Error> {
        self.0.truncate(size)
    }

    fn lock(&mut self, lock: sqlite_vfs::LockKind) -> Result<bool, io::Error> {
        self.0.lock(to_our_lock_level(lock))?;
        Ok(true)
    }

    fn unlock(&mut self, lock: sqlite_vfs::LockKind) -> Result<bool, io::Error> {
        self.0.unlock(to_our_lock_level(lock))?;
        Ok(true)
    }

    fn reserved(&mut self) -> Result<bool, io::Error> {
        Ok(self.0.reserved())
    }

    fn current_lock(&self) -> Result<sqlite_vfs::LockKind, io::Error> {
        Ok(from_our_lock_level(self.0.current_lock()))
    }

    fn wal_index(&self, _readonly: bool) -> Result<Self::WalIndex, io::Error> {
        Ok(WalIndexStub)
    }
}

// ---------------------------------------------------------------------------
// WAL index stub (WAL is not supported through this adapter)
// ---------------------------------------------------------------------------

/// No-op WAL index — disables WAL mode for VFS implementations registered
/// through this adapter.
struct WalIndexStub;

impl sqlite_vfs::wip::WalIndex for WalIndexStub {
    fn enabled() -> bool {
        false
    }

    fn map(&mut self, _region: u32) -> Result<[u8; 32768], io::Error> {
        Err(io::Error::other("WAL is disabled"))
    }

    fn lock(
        &mut self,
        _locks: Range<u8>,
        _lock: sqlite_vfs::wip::WalIndexLock,
    ) -> Result<bool, io::Error> {
        Err(io::Error::other("WAL is disabled"))
    }

    fn delete(self) -> Result<(), io::Error> {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Enum conversions
// ---------------------------------------------------------------------------

fn to_our_open_kind(kind: sqlite_vfs::OpenKind) -> OpenKind {
    match kind {
        sqlite_vfs::OpenKind::MainDb => OpenKind::MainDb,
        sqlite_vfs::OpenKind::MainJournal
        | sqlite_vfs::OpenKind::SubJournal
        | sqlite_vfs::OpenKind::SuperJournal => OpenKind::Journal,
        sqlite_vfs::OpenKind::Wal => OpenKind::Wal,
        sqlite_vfs::OpenKind::TempDb
        | sqlite_vfs::OpenKind::TempJournal
        | sqlite_vfs::OpenKind::TransientDb => OpenKind::Temp,
    }
}

fn to_our_open_flags(access: sqlite_vfs::OpenAccess) -> OpenFlags {
    match access {
        sqlite_vfs::OpenAccess::Read => OpenFlags::READ_ONLY,
        sqlite_vfs::OpenAccess::Write => OpenFlags::empty(),
        sqlite_vfs::OpenAccess::Create => OpenFlags::CREATE,
        sqlite_vfs::OpenAccess::CreateNew => OpenFlags::CREATE | OpenFlags::EXCLUSIVE,
    }
}

fn to_our_lock_level(lock: sqlite_vfs::LockKind) -> LockLevel {
    match lock {
        sqlite_vfs::LockKind::None => LockLevel::None,
        sqlite_vfs::LockKind::Shared => LockLevel::Shared,
        sqlite_vfs::LockKind::Reserved => LockLevel::Reserved,
        sqlite_vfs::LockKind::Pending => LockLevel::Pending,
        sqlite_vfs::LockKind::Exclusive => LockLevel::Exclusive,
    }
}

fn from_our_lock_level(level: LockLevel) -> sqlite_vfs::LockKind {
    match level {
        LockLevel::None => sqlite_vfs::LockKind::None,
        LockLevel::Shared => sqlite_vfs::LockKind::Shared,
        LockLevel::Reserved => sqlite_vfs::LockKind::Reserved,
        LockLevel::Pending => sqlite_vfs::LockKind::Pending,
        LockLevel::Exclusive => sqlite_vfs::LockKind::Exclusive,
    }
}

// ---------------------------------------------------------------------------
// Public registration entry point
// ---------------------------------------------------------------------------

/// Registers a [`Vfs`] implementation with `SQLite` on native targets.
///
/// The `name` uniquely identifies the VFS so that connections can request it
/// via `PRAGMA vfs_name` or `sqlite3_open_v2`. When `as_default` is `true`
/// the VFS becomes the default for all new connections.
///
/// # Bounds
///
/// `Sync` is required by the underlying `sqlite-vfs` crate because `SQLite`
/// may invoke VFS callbacks from any thread.
///
/// # Errors
///
/// Returns an error if the name contains an interior NUL byte or if the
/// `SQLite` `sqlite3_vfs_register` call fails.
pub fn register<V>(
    name: &str,
    vfs: V,
    as_default: bool,
) -> Result<(), sqlite_vfs::RegisterError>
where
    V: Vfs + Sync + 'static,
    V::File: Sync,
{
    sqlite_vfs::register(name, VfsAdapter(vfs), as_default)
}
