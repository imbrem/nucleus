#![allow(unsafe_code)]
//! FFI adapter from [`Vfs`] implementations to `SQLite`'s C API.
//!
//! This module builds the FFI trampolines that bridge our safe [`Vfs`] and
//! [`File`] traits to the `sqlite3_vfs` / `sqlite3_io_methods` C interface.
//! Registration policy and name ownership live in the sibling registry
//! module; this module contains only the `SQLite` ABI implementation.
//!
//! # Architecture
//!
//! Two heap-allocated structs carry state across the FFI boundary:
//!
//! - [`VfsState`] holds the `Vfs` implementation and the `sqlite3_io_methods`
//!   table.  A raw pointer to it is stored in `sqlite3_vfs.pAppData`.  It is
//!   intentionally leaked and lives for the process lifetime.
//!
//! - [`FileState`] is a `#[repr(C)]` struct whose first field is
//!   `sqlite3_file`.  `SQLite` allocates `szOsFile` bytes for each open
//!   file; we set that to `size_of::<FileState>()` so the memory is ours to
//!   use.  The `file` field is [`MaybeUninit`] because `SQLite` allocates
//!   the struct first and only later calls `xOpen` to initialise it.
//!
//! Because [`File`] methods take `&self`, no `Mutex` is needed around the
//! file handle — implementations provide their own interior mutability
//! where required.

use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::slice;
use std::time::{Duration, Instant};

use crate::ffi;

use super::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, SyncFlags, Vfs,
};

/// Maximum pathname length exposed to `SQLite`.
const MAX_PATH: usize = 512;

fn catch_callback<T>(fallback: T, callback: impl FnOnce() -> T) -> T {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(callback)).unwrap_or(fallback)
}

// ---------------------------------------------------------------------------
// State structs
// ---------------------------------------------------------------------------

/// Heap-allocated state that lives for the lifetime of the registered VFS.
/// A raw pointer to this is stored in `sqlite3_vfs.pAppData`.
struct VfsState<V: Vfs> {
    /// Kept alive so the `zName` pointer in `sqlite3_vfs` remains valid.
    #[allow(dead_code)]
    name: CString,
    vfs: V,
    io_methods: ffi::sqlite3_io_methods,
    fallback: *mut ffi::sqlite3_vfs,
}

/// Per-open-file state.  The first field **must** be `sqlite3_file` so that
/// a `*mut FileState<V>` and a `*mut sqlite3_file` are interchangeable
/// (`#[repr(C)]` guarantees no leading padding).
#[repr(C)]
struct FileState<V: Vfs> {
    base: ffi::sqlite3_file,
    /// The file handle.  [`MaybeUninit`] because `SQLite` allocates this
    /// struct (via `szOsFile`) before calling `xOpen` to initialise it;
    /// `xClose` drops it in place.
    file: MaybeUninit<V::File>,
    /// Back-pointer to the owning VFS state (valid for the process lifetime).
    vfs_state: *const VfsState<V>,
}

impl<V: Vfs> FileState<V> {
    /// Returns a shared reference to the initialised file handle.
    ///
    /// # Safety
    ///
    /// The caller must ensure `self.file` has been initialised (i.e. `xOpen`
    /// has run and `xClose` has not yet run).
    unsafe fn file(&self) -> &V::File {
        unsafe { self.file.assume_init_ref() }
    }
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

/// Installs one adapter in `SQLite`'s process-global VFS list.
///
/// The caller owns duplicate-name policy and must serialize the
/// find-then-register sequence.
///
#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
pub(super) fn register<V: Vfs + Send + Sync + 'static>(
    name: CString,
    vfs: V,
    as_default: bool,
) -> Result<*mut ffi::sqlite3_vfs, c_int> {
    let name_ptr = name.as_ptr();
    // SAFETY: a null name asks SQLite for the current default VFS. Capture it
    // before registration so callbacks can delegate platform services without
    // recursing if this VFS becomes the new default.
    let fallback = unsafe { ffi::sqlite3_vfs_find(ptr::null()) };
    let io_methods = ffi::sqlite3_io_methods {
        iVersion: 1,
        xClose: Some(x_close::<V>),
        xRead: Some(x_read::<V>),
        xWrite: Some(x_write::<V>),
        xTruncate: Some(x_truncate::<V>),
        xSync: Some(x_sync::<V>),
        xFileSize: Some(x_file_size::<V>),
        xLock: Some(x_lock::<V>),
        xUnlock: Some(x_unlock::<V>),
        xCheckReservedLock: Some(x_check_reserved_lock::<V>),
        xFileControl: Some(x_file_control),
        xSectorSize: Some(x_sector_size::<V>),
        xDeviceCharacteristics: Some(x_device_characteristics::<V>),
        xShmMap: None,
        xShmLock: None,
        xShmBarrier: None,
        xShmUnmap: None,
        xFetch: None,
        xUnfetch: None,
    };

    // `c_name` is moved into the leaked `VfsState`; `name_ptr` remains
    // valid because `CString` stores its data on the heap and moving the
    // owner does not move the underlying buffer.
    let state = Box::into_raw(Box::new(VfsState {
        name,
        vfs,
        io_methods,
        fallback,
    }));

    let vfs_obj = Box::into_raw(Box::new(ffi::sqlite3_vfs {
        iVersion: 2,
        szOsFile: mem::size_of::<FileState<V>>() as c_int,
        mxPathname: MAX_PATH as c_int,
        pNext: ptr::null_mut(),
        zName: name_ptr,
        pAppData: state.cast::<c_void>(),
        xOpen: Some(x_open::<V>),
        xDelete: Some(x_delete::<V>),
        xAccess: Some(x_access::<V>),
        xFullPathname: Some(x_full_pathname::<V>),
        xDlOpen: None,
        xDlError: None,
        xDlSym: None,
        xDlClose: None,
        xRandomness: Some(x_randomness::<V>),
        xSleep: Some(x_sleep),
        xCurrentTime: Some(x_current_time),
        xGetLastError: Some(x_get_last_error),
        xCurrentTimeInt64: Some(x_current_time_int64),
        xSetSystemCall: None,
        xGetSystemCall: None,
        xNextSystemCall: None,
    }));

    // SAFETY: `vfs_obj` points to a valid, fully-initialised `sqlite3_vfs`.
    // SAFETY: both allocations are fully initialized and intentionally live
    // until process exit after successful SQLite registration.
    let rc = unsafe { ffi::sqlite3_vfs_register(vfs_obj, c_int::from(as_default)) };
    if rc != ffi::SQLITE_OK {
        // SAFETY: registration failed — `SQLite` has not taken ownership.
        unsafe {
            drop(Box::from_raw(vfs_obj));
            drop(Box::from_raw(state));
        }
        return Err(rc);
    }
    Ok(vfs_obj)
}

pub(super) fn name_exists(name: &CStr) -> bool {
    // SAFETY: name is NUL-terminated and lives across this read-only call.
    !unsafe { ffi::sqlite3_vfs_find(name.as_ptr()) }.is_null()
}

// ---------------------------------------------------------------------------
// Helpers: recover state pointers
// ---------------------------------------------------------------------------

/// Recovers the [`VfsState`] from a `sqlite3_vfs` pointer.
///
/// # Safety
///
/// `p_vfs` must point to a live `sqlite3_vfs` whose `pAppData` was set by
/// [`register`].
unsafe fn vfs_state<'a, V: Vfs>(p_vfs: *mut ffi::sqlite3_vfs) -> &'a VfsState<V> {
    unsafe { &*((*p_vfs).pAppData.cast::<VfsState<V>>()) }
}

/// Recovers the [`FileState`] from a `sqlite3_file` pointer.
///
/// # Safety
///
/// `p_file` must point to a `FileState<V>` whose `file` field has been
/// initialised by `x_open` and not yet dropped by `x_close`.
unsafe fn file_state<'a, V: Vfs>(p_file: *mut ffi::sqlite3_file) -> &'a FileState<V> {
    unsafe { &*(p_file.cast::<FileState<V>>()) }
}

// ---------------------------------------------------------------------------
// Helpers: enum conversions
// ---------------------------------------------------------------------------

fn lock_level_from_c(level: c_int) -> LockLevel {
    match level {
        ffi::SQLITE_LOCK_SHARED => LockLevel::Shared,
        ffi::SQLITE_LOCK_RESERVED => LockLevel::Reserved,
        ffi::SQLITE_LOCK_PENDING => LockLevel::Pending,
        ffi::SQLITE_LOCK_EXCLUSIVE => LockLevel::Exclusive,
        _ => LockLevel::None,
    }
}

fn open_kind_from_flags(flags: c_int) -> OpenKind {
    if flags & ffi::SQLITE_OPEN_MAIN_DB != 0 {
        OpenKind::MainDb
    } else if flags & ffi::SQLITE_OPEN_MAIN_JOURNAL != 0 {
        OpenKind::Journal
    } else if flags & ffi::SQLITE_OPEN_WAL != 0 {
        OpenKind::Wal
    } else {
        OpenKind::Temp
    }
}

fn open_flags_from_c(flags: c_int) -> OpenFlags {
    let mut out = OpenFlags::empty();
    if flags & ffi::SQLITE_OPEN_CREATE != 0 {
        out |= OpenFlags::CREATE;
    }
    if flags & ffi::SQLITE_OPEN_EXCLUSIVE != 0 {
        out |= OpenFlags::EXCLUSIVE;
    }
    if flags & ffi::SQLITE_OPEN_READONLY != 0 {
        out |= OpenFlags::READ_ONLY;
    }
    if flags & ffi::SQLITE_OPEN_READWRITE != 0 {
        out |= OpenFlags::READ_WRITE;
    }
    if flags & ffi::SQLITE_OPEN_DELETEONCLOSE != 0 {
        out |= OpenFlags::DELETE_ON_CLOSE;
    }
    out
}

fn open_flags_to_c(flags: OpenFlags) -> c_int {
    let mut out = 0;
    if flags.contains(OpenFlags::CREATE) {
        out |= ffi::SQLITE_OPEN_CREATE;
    }
    if flags.contains(OpenFlags::EXCLUSIVE) {
        out |= ffi::SQLITE_OPEN_EXCLUSIVE;
    }
    if flags.contains(OpenFlags::READ_ONLY) {
        out |= ffi::SQLITE_OPEN_READONLY;
    }
    if flags.contains(OpenFlags::READ_WRITE) {
        out |= ffi::SQLITE_OPEN_READWRITE;
    }
    if flags.contains(OpenFlags::DELETE_ON_CLOSE) {
        out |= ffi::SQLITE_OPEN_DELETEONCLOSE;
    }
    out
}

fn sync_flags_from_c(flags: c_int) -> SyncFlags {
    if flags & ffi::SQLITE_SYNC_DATAONLY != 0 {
        SyncFlags::DataOnly
    } else if flags & 0x0F == ffi::SQLITE_SYNC_FULL {
        SyncFlags::Full
    } else {
        SyncFlags::Normal
    }
}

fn access_check_from_c(flags: c_int) -> AccessCheck {
    match flags {
        ffi::SQLITE_ACCESS_READWRITE => AccessCheck::ReadWrite,
        ffi::SQLITE_ACCESS_READ => AccessCheck::Read,
        _ => AccessCheck::Exists,
    }
}

// ---------------------------------------------------------------------------
// VFS trampolines
// ---------------------------------------------------------------------------

/// # Safety
///
/// Called by `SQLite`.  All pointer arguments are valid per the `xOpen`
/// contract.
#[allow(clippy::cast_sign_loss)]
unsafe extern "C" fn x_open<V: Vfs + Send + Sync + 'static>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_name: *const c_char,
    p_file: *mut ffi::sqlite3_file,
    flags: c_int,
    p_out_flags: *mut c_int,
) -> c_int {
    // SQLite requires pMethods to remain null when xOpen fails.
    unsafe { (*p_file).pMethods = ptr::null() };
    let state = unsafe { vfs_state::<V>(p_vfs) };

    let path = if z_name.is_null() {
        None
    } else {
        match unsafe { CStr::from_ptr(z_name) }.to_str() {
            Ok(s) => Some(s),
            Err(_) => return ffi::SQLITE_CANTOPEN,
        }
    };

    let kind = open_kind_from_flags(flags);
    // Version-1 I/O methods do not provide shared-memory callbacks, so WAL
    // files cannot be served correctly by this first-pass adapter.
    if kind == OpenKind::Wal {
        return ffi::SQLITE_CANTOPEN;
    }

    let Ok(opened) = catch_callback(Err(std::io::Error::other("VFS callback panicked")), || {
        state.vfs.open(path, kind, open_flags_from_c(flags))
    }) else {
        return ffi::SQLITE_CANTOPEN;
    };

    // SAFETY: `SQLite` allocated `szOsFile` bytes at `p_file`, which equals
    // `size_of::<FileState<V>>()`.  We write each field individually to
    // avoid requiring the whole struct to be initialised up front.
    let fs = p_file.cast::<FileState<V>>();
    unsafe {
        ptr::addr_of_mut!((*fs).base).write(ffi::sqlite3_file {
            pMethods: &raw const state.io_methods,
        });
        ptr::addr_of_mut!((*fs).file).write(MaybeUninit::new(opened.file));
        ptr::addr_of_mut!((*fs).vfs_state).write(state);
    }

    if !p_out_flags.is_null() {
        unsafe { *p_out_flags = open_flags_to_c(opened.flags) };
    }

    ffi::SQLITE_OK
}

/// # Safety
///
/// Called by `SQLite`.  Pointer arguments are valid per the `xDelete`
/// contract.
unsafe extern "C" fn x_delete<V: Vfs + Send + Sync + 'static>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    sync_dir: c_int,
) -> c_int {
    let state = unsafe { vfs_state::<V>(p_vfs) };
    let Ok(path) = unsafe { CStr::from_ptr(z_path) }.to_str() else {
        return ffi::SQLITE_IOERR_DELETE;
    };
    match catch_callback(Err(std::io::Error::other("VFS callback panicked")), || {
        state.vfs.delete(path, sync_dir != 0)
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_DELETE,
    }
}

/// # Safety
///
/// Called by `SQLite`.  Pointer arguments are valid per the `xAccess`
/// contract.
unsafe extern "C" fn x_access<V: Vfs + Send + Sync + 'static>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    flags: c_int,
    p_res_out: *mut c_int,
) -> c_int {
    let state = unsafe { vfs_state::<V>(p_vfs) };
    let Ok(path) = unsafe { CStr::from_ptr(z_path) }.to_str() else {
        return ffi::SQLITE_IOERR_ACCESS;
    };
    match catch_callback(Err(std::io::Error::other("VFS callback panicked")), || {
        state.vfs.access(path, access_check_from_c(flags))
    }) {
        Ok(result) => {
            unsafe { *p_res_out = c_int::from(result) };
            ffi::SQLITE_OK
        }
        Err(_) => ffi::SQLITE_IOERR_ACCESS,
    }
}

/// # Safety
///
/// Called by `SQLite`.  Pointer arguments are valid per the
/// `xFullPathname` contract.
#[allow(clippy::cast_sign_loss)]
unsafe extern "C" fn x_full_pathname<V: Vfs + Send + Sync + 'static>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    n_out: c_int,
    z_out: *mut c_char,
) -> c_int {
    let state = unsafe { vfs_state::<V>(p_vfs) };
    let Ok(path) = unsafe { CStr::from_ptr(z_path) }.to_str() else {
        return ffi::SQLITE_ERROR;
    };
    let Ok(full) = catch_callback(Err(std::io::Error::other("VFS callback panicked")), || {
        state.vfs.full_pathname(path)
    }) else {
        return ffi::SQLITE_ERROR;
    };
    let Ok(c_full) = CString::new(full) else {
        return ffi::SQLITE_ERROR;
    };
    let bytes = c_full.as_bytes_with_nul();
    if bytes.len() > n_out as usize {
        return ffi::SQLITE_CANTOPEN;
    }
    let out = unsafe { slice::from_raw_parts_mut(z_out.cast::<u8>(), bytes.len()) };
    out.copy_from_slice(bytes);
    ffi::SQLITE_OK
}

#[allow(clippy::cast_sign_loss)]
unsafe extern "C" fn x_randomness<V: Vfs>(
    p_vfs: *mut ffi::sqlite3_vfs,
    n_byte: c_int,
    z_out: *mut c_char,
) -> c_int {
    let state = unsafe { vfs_state::<V>(p_vfs) };
    let Some(randomness) = (unsafe { state.fallback.as_ref() }).and_then(|vfs| vfs.xRandomness)
    else {
        return 0;
    };
    unsafe { randomness(state.fallback, n_byte, z_out) }
}

unsafe extern "C" fn x_sleep(_p_vfs: *mut ffi::sqlite3_vfs, microseconds: c_int) -> c_int {
    let requested = u64::try_from(microseconds).unwrap_or(0);
    let start = Instant::now();
    std::thread::sleep(Duration::from_micros(requested));
    i32::try_from(start.elapsed().as_micros()).unwrap_or(i32::MAX)
}

unsafe extern "C" fn x_current_time(p_vfs: *mut ffi::sqlite3_vfs, p_time_out: *mut f64) -> c_int {
    let mut ms: ffi::sqlite3_int64 = 0;
    unsafe { x_current_time_int64(p_vfs, &raw mut ms) };
    #[allow(clippy::cast_precision_loss)]
    unsafe {
        *p_time_out = ms as f64 / 86_400_000.0;
    };
    ffi::SQLITE_OK
}

#[allow(clippy::cast_possible_truncation)]
unsafe extern "C" fn x_current_time_int64(
    _p_vfs: *mut ffi::sqlite3_vfs,
    p: *mut ffi::sqlite3_int64,
) -> c_int {
    // Milliseconds from Julian day 0 to the Unix epoch.
    const UNIX_EPOCH_JULIAN_MS: i64 = 24_405_875 * 8_640_000;
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as i64);
    unsafe { *p = now_ms + UNIX_EPOCH_JULIAN_MS };
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_get_last_error(
    _p_vfs: *mut ffi::sqlite3_vfs,
    _n_byte: c_int,
    _z_err_msg: *mut c_char,
) -> c_int {
    0
}

// ---------------------------------------------------------------------------
// File (io_methods) trampolines
// ---------------------------------------------------------------------------

/// # Safety
///
/// Called by `SQLite` exactly once per successful `xOpen`.  After this call
/// the `FileState`'s `file` field is invalid.
unsafe extern "C" fn x_close<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
) -> c_int {
    let fs = p_file.cast::<FileState<V>>();
    // SAFETY: the file was initialised in `x_open` and `SQLite` guarantees
    // `xClose` is called exactly once.
    catch_callback(ffi::SQLITE_IOERR_CLOSE, || {
        // SAFETY: the file was initialized in x_open and this callback owns
        // its single drop.
        unsafe { ptr::drop_in_place((*fs).file.as_mut_ptr()) };
        ffi::SQLITE_OK
    })
}

#[allow(clippy::cast_sign_loss)]
unsafe extern "C" fn x_read<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    z_buf: *mut c_void,
    i_amt: c_int,
    i_ofst: ffi::sqlite3_int64,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    let buf = unsafe { slice::from_raw_parts_mut(z_buf.cast::<u8>(), i_amt as usize) };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.read(buf, i_ofst.cast_unsigned())
    }) {
        Ok(read) if read <= buf.len() => {
            buf[read..].fill(0);
            if read == buf.len() {
                ffi::SQLITE_OK
            } else {
                ffi::SQLITE_IOERR_SHORT_READ
            }
        }
        Ok(_) | Err(_) => ffi::SQLITE_IOERR_READ,
    }
}

#[allow(clippy::cast_sign_loss)]
unsafe extern "C" fn x_write<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    z_buf: *const c_void,
    i_amt: c_int,
    i_ofst: ffi::sqlite3_int64,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    let buf = unsafe { slice::from_raw_parts(z_buf.cast::<u8>(), i_amt as usize) };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.write(buf, i_ofst.cast_unsigned())
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_WRITE,
    }
}

unsafe extern "C" fn x_truncate<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    size: ffi::sqlite3_int64,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.truncate(size.cast_unsigned())
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_TRUNCATE,
    }
}

unsafe extern "C" fn x_sync<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    flags: c_int,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.sync(sync_flags_from_c(flags))
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_FSYNC,
    }
}

#[allow(clippy::cast_possible_wrap)]
unsafe extern "C" fn x_file_size<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    p_size: *mut ffi::sqlite3_int64,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.file_size()
    }) {
        Ok(size) => {
            unsafe { *p_size = size.cast_signed() };
            ffi::SQLITE_OK
        }
        Err(_) => ffi::SQLITE_IOERR_FSTAT,
    }
}

unsafe extern "C" fn x_lock<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    e_lock: c_int,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.lock(lock_level_from_c(e_lock))
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_LOCK,
    }
}

unsafe extern "C" fn x_unlock<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    e_lock: c_int,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    match catch_callback(Err(std::io::Error::other("file callback panicked")), || {
        file.unlock(lock_level_from_c(e_lock))
    }) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_UNLOCK,
    }
}

unsafe extern "C" fn x_check_reserved_lock<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
    p_res_out: *mut c_int,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    let reserved = catch_callback(false, || file.reserved());
    unsafe { *p_res_out = c_int::from(reserved) };
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_file_control(
    _p_file: *mut ffi::sqlite3_file,
    _op: c_int,
    _p_arg: *mut c_void,
) -> c_int {
    ffi::SQLITE_NOTFOUND
}

#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
unsafe extern "C" fn x_sector_size<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    let size = catch_callback(0, || file.sector_size());
    if size == 0 { 4096 } else { size as c_int }
}

#[allow(clippy::cast_possible_wrap)]
unsafe extern "C" fn x_device_characteristics<V: Vfs + Send + Sync + 'static>(
    p_file: *mut ffi::sqlite3_file,
) -> c_int {
    let file = unsafe { file_state::<V>(p_file).file() };
    catch_callback(DeviceCharacteristics::default(), || {
        file.device_characteristics()
    })
    .bits()
    .cast_signed()
}
