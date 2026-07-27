//! Registration adapter for WASM targets using the `rsqlite-vfs` crate.
//!
//! Bridges our [`Vfs`](super::Vfs) / [`File`](super::File) traits to the
//! store-based VFS model of `rsqlite-vfs` and delegates to
//! [`rsqlite_vfs::register_vfs`] for the actual registration.
//!
//! The `rsqlite_vfs` traits require calling `unsafe` helper methods
//! (`app_data`, `SQLiteVfsFile::name`) that dereference raw pointers managed
//! by the C side of `SQLite`. This module allows `unsafe_code` for those
//! specific call sites.
#![allow(unsafe_code)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::time::Duration;

use rsqlite_vfs::{
    SQLiteIoMethods, SQLiteVfs, SQLiteVfsFile, VfsError, VfsFile, VfsResult, VfsStore,
};

use super::{AccessCheck, File, OpenFlags, OpenKind, Vfs};

// ---------------------------------------------------------------------------
// AppData — holds our Vfs plus the open-file table
// ---------------------------------------------------------------------------

/// Per-VFS state stored in `sqlite3_vfs.pAppData`.
struct AppData<V: Vfs> {
    vfs: V,
    files: RefCell<HashMap<String, WasmFile<V::File>>>,
}

// ---------------------------------------------------------------------------
// File wrapper — bridges our File to rsqlite_vfs::VfsFile
// ---------------------------------------------------------------------------

/// Wraps a [`File`] in a `RefCell` so that the immutable-receiver
/// `VfsFile::read` can call our mutable-receiver `File::read`.
struct WasmFile<F>(RefCell<F>);

impl<F: File> VfsFile for WasmFile<F> {
    fn read(&self, buf: &mut [u8], offset: usize) -> VfsResult<bool> {
        let mut file = self.0.borrow_mut();
        #[allow(clippy::cast_possible_truncation)] // WASM is 32-bit; files cannot exceed usize.
        let size = file.file_size().map_err(io_to_vfs)? as usize;
        file.read(buf, offset as u64).map_err(io_to_vfs)?;
        // Return false for short reads (triggers SQLITE_IOERR_SHORT_READ).
        Ok(offset + buf.len() <= size)
    }

    fn write(&mut self, buf: &[u8], offset: usize) -> VfsResult<()> {
        self.0
            .borrow_mut()
            .write(buf, offset as u64)
            .map_err(io_to_vfs)
    }

    fn truncate(&mut self, size: usize) -> VfsResult<()> {
        self.0
            .borrow_mut()
            .truncate(size as u64)
            .map_err(io_to_vfs)
    }

    fn flush(&mut self) -> VfsResult<()> {
        self.0
            .borrow_mut()
            .sync(super::SyncFlags::Normal)
            .map_err(io_to_vfs)
    }

    #[allow(clippy::cast_possible_truncation)] // WASM is 32-bit; files cannot exceed usize.
    fn size(&self) -> VfsResult<usize> {
        self.0
            .borrow()
            .file_size()
            .map(|s| s as usize)
            .map_err(io_to_vfs)
    }
}

// ---------------------------------------------------------------------------
// Store — manages open files for the VFS
// ---------------------------------------------------------------------------

/// Implements `VfsStore` by keeping open file handles in a `HashMap` inside
/// [`AppData`] and delegating create/delete to our [`Vfs`].
struct Store<V: Vfs>(PhantomData<V>);

impl<V: Vfs + 'static> VfsStore<WasmFile<V::File>, AppData<V>> for Store<V> {
    fn add_file(
        vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs,
        file: &str,
        flags: i32,
    ) -> VfsResult<()> {
        let app_data = unsafe { Self::app_data(vfs) };
        let kind = flags_to_open_kind(flags);
        let open_flags = flags_to_open_flags(flags);
        let f = app_data
            .vfs
            .open(Some(file), kind, open_flags)
            .map_err(io_to_vfs)?;
        app_data
            .files
            .borrow_mut()
            .insert(file.into(), WasmFile(RefCell::new(f)));
        Ok(())
    }

    fn contains_file(
        vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs,
        file: &str,
    ) -> VfsResult<bool> {
        let app_data = unsafe { Self::app_data(vfs) };
        if app_data.files.borrow().contains_key(file) {
            return Ok(true);
        }
        app_data
            .vfs
            .access(file, AccessCheck::Exists)
            .map_err(io_to_vfs)
    }

    fn delete_file(
        vfs: *mut rsqlite_vfs::ffi::sqlite3_vfs,
        file: &str,
    ) -> VfsResult<()> {
        let app_data = unsafe { Self::app_data(vfs) };
        app_data.files.borrow_mut().remove(file);
        app_data
            .vfs
            .delete(file, false)
            .map_err(io_to_vfs)
    }

    fn with_file<F: Fn(&WasmFile<V::File>) -> VfsResult<i32>>(
        vfs_file: &SQLiteVfsFile,
        f: F,
    ) -> VfsResult<i32> {
        let name = unsafe { vfs_file.name() };
        let app_data = unsafe { Self::app_data(vfs_file.vfs) };
        let files = app_data.files.borrow();
        let file = files.get(name).ok_or_else(|| {
            VfsError::new(
                rsqlite_vfs::ffi::SQLITE_IOERR,
                format!("{name} not found"),
            )
        })?;
        f(file)
    }

    fn with_file_mut<F: Fn(&mut WasmFile<V::File>) -> VfsResult<i32>>(
        vfs_file: &SQLiteVfsFile,
        f: F,
    ) -> VfsResult<i32> {
        let name = unsafe { vfs_file.name() };
        let app_data = unsafe { Self::app_data(vfs_file.vfs) };
        let mut files = app_data.files.borrow_mut();
        let file = files.get_mut(name).ok_or_else(|| {
            VfsError::new(
                rsqlite_vfs::ffi::SQLITE_IOERR,
                format!("{name} not found"),
            )
        })?;
        f(file)
    }
}

// ---------------------------------------------------------------------------
// IO methods marker type
// ---------------------------------------------------------------------------

/// Marker type connecting our file/store types to `rsqlite_vfs`'s IO
/// methods table.
struct Io<V: Vfs>(PhantomData<V>);

impl<V: Vfs + 'static> SQLiteIoMethods for Io<V> {
    type File = WasmFile<V::File>;
    type AppData = AppData<V>;
    type Store = Store<V>;

    const VERSION: core::ffi::c_int = 1;
}

// ---------------------------------------------------------------------------
// SQLiteVfs implementation
// ---------------------------------------------------------------------------

/// Adapter that implements [`SQLiteVfs`] by forwarding platform callbacks to
/// the caller-provided `C: rsqlite_vfs::OsCallback`.
struct VfsAdapter<V: Vfs, C>(PhantomData<(V, C)>);

impl<V, C> SQLiteVfs<Io<V>> for VfsAdapter<V, C>
where
    V: Vfs + 'static,
    C: rsqlite_vfs::OsCallback,
{
    const VERSION: core::ffi::c_int = 1;

    fn sleep(dur: Duration) {
        C::sleep(dur);
    }

    fn random(buf: &mut [u8]) {
        C::random(buf);
    }

    fn epoch_timestamp_in_ms() -> i64 {
        C::epoch_timestamp_in_ms()
    }
}

// ---------------------------------------------------------------------------
// Flag conversions
// ---------------------------------------------------------------------------

fn flags_to_open_kind(flags: i32) -> OpenKind {
    if flags & rsqlite_vfs::ffi::SQLITE_OPEN_MAIN_DB != 0 {
        OpenKind::MainDb
    } else if flags & rsqlite_vfs::ffi::SQLITE_OPEN_MAIN_JOURNAL != 0 {
        OpenKind::Journal
    } else if flags & rsqlite_vfs::ffi::SQLITE_OPEN_WAL != 0 {
        OpenKind::Wal
    } else {
        OpenKind::Temp
    }
}

fn flags_to_open_flags(flags: i32) -> OpenFlags {
    let mut result = OpenFlags::empty();
    if flags & rsqlite_vfs::ffi::SQLITE_OPEN_CREATE != 0 {
        result |= OpenFlags::CREATE;
    }
    if flags & rsqlite_vfs::ffi::SQLITE_OPEN_EXCLUSIVE != 0 {
        result |= OpenFlags::EXCLUSIVE;
    }
    if flags & rsqlite_vfs::ffi::SQLITE_OPEN_READONLY != 0 {
        result |= OpenFlags::READ_ONLY;
    }
    if flags & rsqlite_vfs::ffi::SQLITE_OPEN_DELETEONCLOSE != 0 {
        result |= OpenFlags::DELETE_ON_CLOSE;
    }
    result
}

// ---------------------------------------------------------------------------
// Error conversion
// ---------------------------------------------------------------------------

#[allow(clippy::needless_pass_by_value)] // Must be by-value for use with `map_err`.
fn io_to_vfs(err: std::io::Error) -> VfsError {
    VfsError::new(rsqlite_vfs::ffi::SQLITE_IOERR, err.to_string())
}

// ---------------------------------------------------------------------------
// Public registration entry point
// ---------------------------------------------------------------------------

/// Registers a [`Vfs`] implementation with `SQLite` on WASM targets.
///
/// `C` supplies the platform-specific callbacks (random, sleep, time) that
/// `rsqlite-vfs` needs. See [`rsqlite_vfs::OsCallback`] for the required
/// interface.
///
/// The `name` uniquely identifies the VFS so that connections can request it
/// via `sqlite3_open_v2`. When `as_default` is `true` the VFS becomes the
/// default for all new connections.
///
/// # Errors
///
/// Returns an error if the name cannot be converted to a C string or if the
/// `SQLite` `sqlite3_vfs_register` call fails.
pub fn register<V, C>(
    name: &str,
    vfs: V,
    as_default: bool,
) -> Result<(), rsqlite_vfs::RegisterVfsError>
where
    V: Vfs + 'static,
    C: rsqlite_vfs::OsCallback,
{
    let app_data = AppData {
        vfs,
        files: RefCell::new(HashMap::new()),
    };
    rsqlite_vfs::register_vfs::<Io<V>, VfsAdapter<V, C>>(name, app_data, as_default)?;
    Ok(())
}
