#![allow(unsafe_code)]
//! Registration of [`Vfs`] implementations with SQLite's C API.
//!
//! This module builds the FFI bridge that allows a safe [`Vfs`] + [`File`]
//! implementation to be used by SQLite connections.  Call [`register`] once
//! at startup; the VFS will be available to any subsequent
//! `Connection::open_with_flags_and_vfs` call.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::io;
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::slice;
use std::sync::Mutex;

use crate::ffi;

use super::*;

/// Maximum pathname length exposed to SQLite.
const MAX_PATH: usize = 512;

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
}

/// Per-open-file state.  The first field **must** be `sqlite3_file` so that
/// a pointer to `FileState` is also a valid pointer to `sqlite3_file`.
#[repr(C)]
struct FileState<V: Vfs> {
    base: ffi::sqlite3_file,
    /// The actual file handle.  `MaybeUninit` because SQLite allocates this
    /// struct (via `szOsFile`) and only later calls `xOpen` to initialise it.
    file: MaybeUninit<Mutex<V::File>>,
    /// Back-pointer to the owning VFS state (valid for the program lifetime).
    vfs_state: *const VfsState<V>,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Register a [`Vfs`] implementation with SQLite.
///
/// After a successful call, the VFS named `name` can be selected when opening
/// a database:
///
/// ```ignore
/// register("myvfs", MyVfs::new(), false)?;
/// let conn = Connection::open_with_flags_and_vfs(
///     ":memory:",
///     OpenFlags::default(),
///     "myvfs",
/// )?;
/// ```
///
/// If `as_default` is `true` the VFS becomes the default for all new
/// connections.
///
/// # Leaks
///
/// The `VfsState` and `sqlite3_vfs` structs are intentionally leaked (they
/// must live as long as the SQLite library itself).  There is currently no
/// `unregister` counterpart.
pub fn register<V>(name: &str, vfs: V, as_default: bool) -> io::Result<()>
where
    V: Vfs + Sync + 'static,
    V::File: Send,
{
    let name =
        CString::new(name).map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;
    let name_ptr = name.as_ptr();

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
        xFileControl: Some(x_file_control::<V>),
        xSectorSize: Some(x_sector_size::<V>),
        xDeviceCharacteristics: Some(x_device_characteristics::<V>),
        // iVersion 1 does not use shared-memory methods.
        xShmMap: None,
        xShmLock: None,
        xShmBarrier: None,
        xShmUnmap: None,
        xFetch: None,
        xUnfetch: None,
    };

    let state = Box::into_raw(Box::new(VfsState {
        name,
        vfs,
        io_methods,
    }));

    let vfs_obj = Box::into_raw(Box::new(ffi::sqlite3_vfs {
        iVersion: 2,
        szOsFile: mem::size_of::<FileState<V>>() as c_int,
        mxPathname: MAX_PATH as c_int,
        pNext: ptr::null_mut(),
        zName: name_ptr,
        pAppData: state as *mut c_void,
        xOpen: Some(x_open::<V>),
        xDelete: Some(x_delete::<V>),
        xAccess: Some(x_access::<V>),
        xFullPathname: Some(x_full_pathname::<V>),
        xDlOpen: None,
        xDlError: None,
        xDlSym: None,
        xDlClose: None,
        xRandomness: Some(x_randomness::<V>),
        xSleep: Some(x_sleep::<V>),
        xCurrentTime: Some(x_current_time::<V>),
        xGetLastError: Some(x_get_last_error::<V>),
        xCurrentTimeInt64: Some(x_current_time_int64::<V>),
        xSetSystemCall: None,
        xGetSystemCall: None,
        xNextSystemCall: None,
    }));

    // SAFETY: `vfs_obj` points to a valid, fully-initialised `sqlite3_vfs`.
    let rc = unsafe { ffi::sqlite3_vfs_register(vfs_obj, as_default as c_int) };
    if rc != ffi::SQLITE_OK {
        // SAFETY: we just created these; nobody else holds a reference.
        unsafe {
            drop(Box::from_raw(vfs_obj));
            drop(Box::from_raw(state));
        }
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("sqlite3_vfs_register failed with code {rc}"),
        ));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers: recover state pointers
// ---------------------------------------------------------------------------

/// # Safety
///
/// `p_vfs` must point to a live `sqlite3_vfs` whose `pAppData` was set by
/// [`register`].
unsafe fn vfs_state<'a, V: Vfs>(p_vfs: *mut ffi::sqlite3_vfs) -> Option<&'a VfsState<V>> {
    // SAFETY: caller guarantees `p_vfs` is valid.
    let vfs = unsafe { p_vfs.as_ref()? };
    // SAFETY: `pAppData` was set to a `Box::into_raw(Box::new(VfsState))`.
    unsafe { (vfs.pAppData as *const VfsState<V>).as_ref() }
}

/// # Safety
///
/// `p_file` must point to a `FileState<V>` that was initialised by `x_open`.
unsafe fn file_state<'a, V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
) -> Option<&'a mut FileState<V>> {
    // SAFETY: `p_file` is the first field of a `FileState` due to `#[repr(C)]`.
    unsafe { (p_file as *mut FileState<V>).as_mut() }
}

// ---------------------------------------------------------------------------
// Helpers: enum conversions
// ---------------------------------------------------------------------------

fn lock_level_from_c(level: c_int) -> LockLevel {
    match level {
        ffi::SQLITE_LOCK_NONE => LockLevel::None,
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
        // TEMP_DB, TEMP_JOURNAL, TRANSIENT_DB, SUBJOURNAL, SUPER_JOURNAL
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
    if flags & ffi::SQLITE_OPEN_DELETEONCLOSE != 0 {
        out |= OpenFlags::DELETE_ON_CLOSE;
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

unsafe extern "C" fn x_open<V>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_name: *const c_char,
    p_file: *mut ffi::sqlite3_file,
    flags: c_int,
    p_out_flags: *mut c_int,
) -> c_int
where
    V: Vfs + Sync + 'static,
    V::File: Send,
{
    // SAFETY: `p_vfs` is guaranteed valid by SQLite during xOpen.
    let state = match unsafe { vfs_state::<V>(p_vfs) } {
        Some(s) => s,
        None => return ffi::SQLITE_CANTOPEN,
    };

    let path = if z_name.is_null() {
        None
    } else {
        // SAFETY: SQLite guarantees `z_name` is a NUL-terminated string.
        match unsafe { CStr::from_ptr(z_name) }.to_str() {
            Ok(s) => Some(s),
            Err(_) => return ffi::SQLITE_CANTOPEN,
        }
    };

    let kind = open_kind_from_flags(flags);
    let open_flags = open_flags_from_c(flags);

    let file = match state.vfs.open(path, kind, open_flags) {
        Ok(f) => f,
        Err(_) => return ffi::SQLITE_CANTOPEN,
    };

    // SAFETY: `p_file` points to a `FileState<V>` allocated by SQLite with
    // size `szOsFile`.
    let out = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_CANTOPEN,
    };

    out.base.pMethods = &state.io_methods;
    out.file.write(Mutex::new(file));
    out.vfs_state = state;

    if !p_out_flags.is_null() {
        // SAFETY: SQLite guarantees `p_out_flags` is writable when non-null.
        unsafe { *p_out_flags = flags };
    }

    ffi::SQLITE_OK
}

unsafe extern "C" fn x_delete<V: Vfs>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    sync_dir: c_int,
) -> c_int {
    let state = match unsafe { vfs_state::<V>(p_vfs) } {
        Some(s) => s,
        None => return ffi::SQLITE_IOERR_DELETE,
    };

    let path = match unsafe { CStr::from_ptr(z_path) }.to_str() {
        Ok(s) => s,
        Err(_) => return ffi::SQLITE_IOERR_DELETE,
    };

    match state.vfs.delete(path, sync_dir != 0) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_DELETE,
    }
}

unsafe extern "C" fn x_access<V: Vfs>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    flags: c_int,
    p_res_out: *mut c_int,
) -> c_int {
    let state = match unsafe { vfs_state::<V>(p_vfs) } {
        Some(s) => s,
        None => return ffi::SQLITE_IOERR_ACCESS,
    };

    let path = match unsafe { CStr::from_ptr(z_path) }.to_str() {
        Ok(s) => s,
        Err(_) => return ffi::SQLITE_IOERR_ACCESS,
    };

    let check = access_check_from_c(flags);
    match state.vfs.access(path, check) {
        Ok(result) => {
            if !p_res_out.is_null() {
                unsafe { *p_res_out = result as c_int };
            }
            ffi::SQLITE_OK
        }
        Err(_) => ffi::SQLITE_IOERR_ACCESS,
    }
}

unsafe extern "C" fn x_full_pathname<V: Vfs>(
    p_vfs: *mut ffi::sqlite3_vfs,
    z_path: *const c_char,
    n_out: c_int,
    z_out: *mut c_char,
) -> c_int {
    let state = match unsafe { vfs_state::<V>(p_vfs) } {
        Some(s) => s,
        None => return ffi::SQLITE_ERROR,
    };

    let path = match unsafe { CStr::from_ptr(z_path) }.to_str() {
        Ok(s) => s,
        Err(_) => return ffi::SQLITE_ERROR,
    };

    let full = match state.vfs.full_pathname(path) {
        Ok(p) => p,
        Err(_) => return ffi::SQLITE_ERROR,
    };

    let c_full = match CString::new(full) {
        Ok(c) => c,
        Err(_) => return ffi::SQLITE_ERROR,
    };

    let bytes = c_full.as_bytes_with_nul();
    if bytes.len() > n_out as usize {
        return ffi::SQLITE_CANTOPEN;
    }

    // SAFETY: SQLite guarantees `z_out` has room for at least `n_out` bytes.
    let out = unsafe { slice::from_raw_parts_mut(z_out as *mut u8, bytes.len()) };
    out.copy_from_slice(bytes);

    ffi::SQLITE_OK
}

unsafe extern "C" fn x_randomness<V: Vfs>(
    _p_vfs: *mut ffi::sqlite3_vfs,
    n_byte: c_int,
    z_out: *mut c_char,
) -> c_int {
    // Fill with zeros -- a minimal implementation.
    let buf = unsafe { slice::from_raw_parts_mut(z_out as *mut u8, n_byte as usize) };
    buf.fill(0);
    n_byte
}

unsafe extern "C" fn x_sleep<V: Vfs>(
    _p_vfs: *mut ffi::sqlite3_vfs,
    microseconds: c_int,
) -> c_int {
    // No-op sleep; return the requested duration.
    microseconds
}

unsafe extern "C" fn x_current_time<V: Vfs>(
    p_vfs: *mut ffi::sqlite3_vfs,
    p_time_out: *mut f64,
) -> c_int {
    let mut ms: ffi::sqlite3_int64 = 0;
    unsafe { x_current_time_int64::<V>(p_vfs, &mut ms) };
    if !p_time_out.is_null() {
        unsafe { *p_time_out = ms as f64 / 86_400_000.0 };
    }
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_current_time_int64<V: Vfs>(
    _p_vfs: *mut ffi::sqlite3_vfs,
    p: *mut ffi::sqlite3_int64,
) -> c_int {
    // Julian day epoch: 24405875 * 8640000 milliseconds from Julian day 0
    // to the Unix epoch (1970-01-01).
    const UNIX_EPOCH_JULIAN_MS: i64 = 24_405_875 * 8_640_000;

    let now_ms = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis() as i64,
        Err(_) => 0,
    };

    if !p.is_null() {
        unsafe { *p = now_ms + UNIX_EPOCH_JULIAN_MS };
    }
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_get_last_error<V: Vfs>(
    _p_vfs: *mut ffi::sqlite3_vfs,
    _n_byte: c_int,
    _z_err_msg: *mut c_char,
) -> c_int {
    0
}

// ---------------------------------------------------------------------------
// File (io_methods) trampolines
// ---------------------------------------------------------------------------

unsafe extern "C" fn x_close<V: Vfs>(p_file: *mut ffi::sqlite3_file) -> c_int {
    if let Some(f) = unsafe { file_state::<V>(p_file) } {
        // Take the value out of MaybeUninit and drop it.
        let file = mem::replace(&mut f.file, MaybeUninit::uninit());
        // SAFETY: the file was initialised in `x_open` and has not been
        // closed yet (SQLite calls xClose exactly once per xOpen).
        drop(unsafe { file.assume_init() });
    }
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_read<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    z_buf: *mut c_void,
    i_amt: c_int,
    i_ofst: ffi::sqlite3_int64,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_READ,
    };

    let buf = unsafe { slice::from_raw_parts_mut(z_buf as *mut u8, i_amt as usize) };
    // SAFETY: the file was initialised in `x_open`.
    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_READ,
    };

    match file.read(buf, i_ofst as u64) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_READ,
    }
}

unsafe extern "C" fn x_write<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    z_buf: *const c_void,
    i_amt: c_int,
    i_ofst: ffi::sqlite3_int64,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_WRITE,
    };

    let buf = unsafe { slice::from_raw_parts(z_buf as *const u8, i_amt as usize) };
    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_WRITE,
    };

    match file.write(buf, i_ofst as u64) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_WRITE,
    }
}

unsafe extern "C" fn x_truncate<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    size: ffi::sqlite3_int64,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_TRUNCATE,
    };

    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_TRUNCATE,
    };

    match file.truncate(size as u64) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_TRUNCATE,
    }
}

unsafe extern "C" fn x_sync<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    flags: c_int,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_FSYNC,
    };

    let sync = sync_flags_from_c(flags);
    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_FSYNC,
    };

    match file.sync(sync) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_FSYNC,
    }
}

unsafe extern "C" fn x_file_size<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    p_size: *mut ffi::sqlite3_int64,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_FSTAT,
    };

    let file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_FSTAT,
    };

    match file.file_size() {
        Ok(size) => {
            if !p_size.is_null() {
                unsafe { *p_size = size as ffi::sqlite3_int64 };
            }
            ffi::SQLITE_OK
        }
        Err(_) => ffi::SQLITE_IOERR_FSTAT,
    }
}

unsafe extern "C" fn x_lock<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    e_lock: c_int,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_LOCK,
    };

    let level = lock_level_from_c(e_lock);
    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_LOCK,
    };

    match file.lock(level) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_LOCK,
    }
}

unsafe extern "C" fn x_unlock<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    e_lock: c_int,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_UNLOCK,
    };

    let level = lock_level_from_c(e_lock);
    let mut file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_UNLOCK,
    };

    match file.unlock(level) {
        Ok(()) => ffi::SQLITE_OK,
        Err(_) => ffi::SQLITE_IOERR_UNLOCK,
    }
}

unsafe extern "C" fn x_check_reserved_lock<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
    p_res_out: *mut c_int,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return ffi::SQLITE_IOERR_CHECKRESERVEDLOCK,
    };

    let file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return ffi::SQLITE_IOERR_CHECKRESERVEDLOCK,
    };

    if !p_res_out.is_null() {
        unsafe { *p_res_out = file.reserved() as c_int };
    }
    ffi::SQLITE_OK
}

unsafe extern "C" fn x_file_control<V: Vfs>(
    _p_file: *mut ffi::sqlite3_file,
    _op: c_int,
    _p_arg: *mut c_void,
) -> c_int {
    ffi::SQLITE_NOTFOUND
}

unsafe extern "C" fn x_sector_size<V: Vfs>(p_file: *mut ffi::sqlite3_file) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return 4096,
    };

    let file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return 4096,
    };

    let size = file.sector_size();
    if size == 0 {
        4096
    } else {
        size as c_int
    }
}

unsafe extern "C" fn x_device_characteristics<V: Vfs>(
    p_file: *mut ffi::sqlite3_file,
) -> c_int {
    let f = match unsafe { file_state::<V>(p_file) } {
        Some(f) => f,
        None => return 0,
    };

    let file = match unsafe { f.file.assume_init_mut() }.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };

    file.device_characteristics().bits() as c_int
}
