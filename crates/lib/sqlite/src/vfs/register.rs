#![allow(unsafe_code)]
//! Registration of [`Vfs`] implementations with `SQLite` via `rsqlite-vfs`.
//!
//! Bridges our safe [`Vfs`]/[`File`] traits to `rsqlite-vfs`'s store-based
//! VFS model and delegates the actual `sqlite3_vfs_register` call to
//! [`rsqlite_vfs::register_vfs`].
//!
//! The `rsqlite-vfs` crate is `#![no_std]` and links against whatever
//! `SQLite` is present (`libsqlite3-sys` on native, `sqlite-wasm-rs` on
//! WASM), so this single implementation works on all targets.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::CString;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Mutex;
use std::time::Duration;

use rsqlite_vfs::ffi::{
    SQLITE_IOERR, SQLITE_OPEN_CREATE, SQLITE_OPEN_DELETEONCLOSE, SQLITE_OPEN_EXCLUSIVE,
    SQLITE_OPEN_MAIN_DB, SQLITE_OPEN_MAIN_JOURNAL, SQLITE_OPEN_READONLY, SQLITE_OPEN_WAL,
};
use rsqlite_vfs::{
    SQLiteIoMethods, SQLiteVfs, SQLiteVfsFile, VfsError, VfsFile, VfsResult, VfsStore,
};

use super::{AccessCheck, File, OpenFlags, OpenKind, Vfs};

// Serialises `register` calls so the find-then-register sequence is atomic
// with respect to other callers of this function.
static REGISTER_LOCK: Mutex<()> = Mutex::new(());

// ---------------------------------------------------------------------------
// AppData — holds our Vfs plus the open-file table
// ---------------------------------------------------------------------------

struct AppData<V: Vfs> {
    vfs: V,
    files: RefCell<HashMap<String, WrappedFile<V::File>>>,
}

// ---------------------------------------------------------------------------
// File wrapper — bridges our File to rsqlite_vfs::VfsFile
// ---------------------------------------------------------------------------

struct WrappedFile<F>(F);

impl<F: File> VfsFile for WrappedFile<F> {
    fn read(&self, buf: &mut [u8], offset: usize) -> VfsResult<bool> {
        #[allow(clippy::cast_possible_truncation)]
        let size = self.0.file_size().map_err(io_to_vfs)? as usize;
        self.0.read(buf, offset as u64).map_err(io_to_vfs)?;
        Ok(offset + buf.len() <= size)
    }

    fn write(&mut self, buf: &[u8], offset: usize) -> VfsResult<()> {
        self.0.write(buf, offset as u64).map_err(io_to_vfs)
    }

    fn truncate(&mut self, size: usize) -> VfsResult<()> {
        self.0.truncate(size as u64).map_err(io_to_vfs)
    }

    fn flush(&mut self) -> VfsResult<()> {
        self.0.sync(super::SyncFlags::Normal).map_err(io_to_vfs)
    }

    #[allow(clippy::cast_possible_truncation)]
    fn size(&self) -> VfsResult<usize> {
        self.0.file_size().map(|s| s as usize).map_err(io_to_vfs)
    }
}

// ---------------------------------------------------------------------------
// Store — manages open files for the VFS
// ---------------------------------------------------------------------------

struct Store<V: Vfs>(PhantomData<V>);

impl<V: Vfs + 'static> VfsStore<WrappedFile<V::File>, AppData<V>> for Store<V> {
    fn add_file(vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs, file: &str, flags: i32) -> VfsResult<()> {
        // SAFETY: `pAppData` was set to a leaked `VfsAppData<AppData<V>>` by
        // `register_vfs`.
        let app_data = unsafe { Self::app_data(vfs) };
        let kind = open_kind_from_flags(flags);
        let open_flags = open_flags_from_c(flags);
        let f = app_data
            .vfs
            .open(Some(file), kind, open_flags)
            .map_err(io_to_vfs)?;
        app_data
            .files
            .borrow_mut()
            .insert(file.into(), WrappedFile(f));
        Ok(())
    }

    fn contains_file(vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs, file: &str) -> VfsResult<bool> {
        // SAFETY: same as `add_file`.
        let app_data = unsafe { Self::app_data(vfs) };
        if app_data.files.borrow().contains_key(file) {
            return Ok(true);
        }
        app_data
            .vfs
            .access(file, AccessCheck::Exists)
            .map_err(io_to_vfs)
    }

    fn delete_file(vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs, file: &str) -> VfsResult<()> {
        // SAFETY: same as `add_file`.
        let app_data = unsafe { Self::app_data(vfs) };
        app_data.files.borrow_mut().remove(file);
        app_data.vfs.delete(file, false).map_err(io_to_vfs)
    }

    fn with_file<F: Fn(&WrappedFile<V::File>) -> VfsResult<i32>>(
        vfs_file: &SQLiteVfsFile,
        f: F,
    ) -> VfsResult<i32> {
        // SAFETY: `name()` dereferences the name pointer that was set during
        // `xOpen` by `rsqlite-vfs`.
        let name = unsafe { vfs_file.name() };
        // SAFETY: same as `add_file`.
        let app_data = unsafe { Self::app_data(vfs_file.vfs) };
        let files = app_data.files.borrow();
        let file = files
            .get(name)
            .ok_or_else(|| VfsError::new(SQLITE_IOERR, format!("{name} not found")))?;
        f(file)
    }

    fn with_file_mut<F: Fn(&mut WrappedFile<V::File>) -> VfsResult<i32>>(
        vfs_file: &SQLiteVfsFile,
        f: F,
    ) -> VfsResult<i32> {
        // SAFETY: same as `with_file`.
        let name = unsafe { vfs_file.name() };
        let app_data = unsafe { Self::app_data(vfs_file.vfs) };
        let mut files = app_data.files.borrow_mut();
        let file = files
            .get_mut(name)
            .ok_or_else(|| VfsError::new(SQLITE_IOERR, format!("{name} not found")))?;
        f(file)
    }
}

// ---------------------------------------------------------------------------
// IO methods and VFS adapter types
// ---------------------------------------------------------------------------

struct Io<V: Vfs>(PhantomData<V>);

impl<V: Vfs + 'static> SQLiteIoMethods for Io<V> {
    type File = WrappedFile<V::File>;
    type AppData = AppData<V>;
    type Store = Store<V>;

    const VERSION: core::ffi::c_int = 1;
}

struct VfsAdapter<V: Vfs>(PhantomData<V>);

impl<V: Vfs + 'static> SQLiteVfs<Io<V>> for VfsAdapter<V> {
    const VERSION: core::ffi::c_int = 1;

    fn sleep(dur: Duration) {
        std::thread::sleep(dur);
    }

    fn random(buf: &mut [u8]) {
        buf.fill(0);
    }

    fn epoch_timestamp_in_ms() -> i64 {
        #[allow(clippy::cast_possible_truncation)]
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_millis() as i64)
    }
}

// ---------------------------------------------------------------------------
// Flag conversions
// ---------------------------------------------------------------------------

fn open_kind_from_flags(flags: i32) -> OpenKind {
    if flags & SQLITE_OPEN_MAIN_DB != 0 {
        OpenKind::MainDb
    } else if flags & SQLITE_OPEN_MAIN_JOURNAL != 0 {
        OpenKind::Journal
    } else if flags & SQLITE_OPEN_WAL != 0 {
        OpenKind::Wal
    } else {
        OpenKind::Temp
    }
}

fn open_flags_from_c(flags: i32) -> OpenFlags {
    let mut out = OpenFlags::empty();
    if flags & SQLITE_OPEN_CREATE != 0 {
        out |= OpenFlags::CREATE;
    }
    if flags & SQLITE_OPEN_EXCLUSIVE != 0 {
        out |= OpenFlags::EXCLUSIVE;
    }
    if flags & SQLITE_OPEN_READONLY != 0 {
        out |= OpenFlags::READ_ONLY;
    }
    if flags & SQLITE_OPEN_DELETEONCLOSE != 0 {
        out |= OpenFlags::DELETE_ON_CLOSE;
    }
    out
}

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

#[allow(clippy::needless_pass_by_value)]
fn io_to_vfs(err: std::io::Error) -> VfsError {
    VfsError::new(SQLITE_IOERR, err.to_string())
}

/// Errors returned by [`register`].
#[derive(Debug)]
pub enum RegisterError {
    /// The VFS name contains an interior NUL byte.
    InvalidName,
    /// A VFS with this name is already registered with `SQLite`.
    AlreadyRegistered,
    /// `sqlite3_vfs_register` failed.
    RegistrationFailed(rsqlite_vfs::RegisterVfsError),
}

impl fmt::Display for RegisterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidName => write!(f, "VFS name contains an interior NUL byte"),
            Self::AlreadyRegistered => {
                write!(f, "a VFS with this name is already registered")
            }
            Self::RegistrationFailed(e) => write!(f, "sqlite3_vfs_register failed: {e}"),
        }
    }
}

impl std::error::Error for RegisterError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::RegistrationFailed(e) => Some(e),
            _ => None,
        }
    }
}

impl From<rsqlite_vfs::RegisterVfsError> for RegisterError {
    fn from(e: rsqlite_vfs::RegisterVfsError) -> Self {
        Self::RegistrationFailed(e)
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Register a [`Vfs`] implementation with `SQLite`.
///
/// After a successful call the VFS named `name` can be selected when opening
/// a database via `Connection::open_with_flags_and_vfs`.
///
/// When `as_default` is `true` the VFS becomes the default for all new
/// connections.
///
/// Returns [`RegisterError::AlreadyRegistered`] if a VFS with the same name
/// is already registered.  Registering two different VFS implementations
/// under the same name is undefined behaviour in `SQLite`, so this check
/// (serialised by an internal mutex) prevents that.
///
/// # Errors
///
/// Returns an error if the name contains a NUL byte, a VFS with the same
/// name already exists, or if `sqlite3_vfs_register` fails.
pub fn register<V: Vfs + 'static>(
    name: &str,
    vfs: V,
    as_default: bool,
) -> Result<(), RegisterError> {
    let c_name = CString::new(name).map_err(|_| RegisterError::InvalidName)?;

    let _guard = REGISTER_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    // SAFETY: `sqlite3_vfs_find` reads the global VFS list; we serialise
    // with the mutex above so no concurrent `register` call can insert
    // between this check and the `register_vfs` below.
    let existing = unsafe { rsqlite_vfs::ffi::sqlite3_vfs_find(c_name.as_ptr()) };
    if !existing.is_null() {
        return Err(RegisterError::AlreadyRegistered);
    }

    let app_data = AppData {
        vfs,
        files: RefCell::new(HashMap::new()),
    };
    rsqlite_vfs::register_vfs::<Io<V>, VfsAdapter<V>>(name, app_data, as_default)?;
    Ok(())
}
