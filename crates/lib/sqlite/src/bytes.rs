#![allow(
    unsafe_code,
    reason = "this module is the owning wrapper around SQLite's allocator"
)]
//! Bytes owned by `SQLite`'s allocator.

use std::fmt;
use std::ops::Deref;
use std::ptr::NonNull;
use std::slice;

use crate::error::{Error, ResultCode};
use crate::ffi;

/// A byte buffer allocated by `SQLite`, freed with `sqlite3_free`.
///
/// Named for whose allocator it belongs to, because that is the whole of what
/// distinguishes it from `bytes::Bytes` and getting the two confused means
/// freeing on the wrong heap.
///
/// Several `SQLite` entry points hand back memory from their own allocator and
/// make the caller responsible for releasing it — `sqlite3_serialize` is the
/// one this crate uses. Returning that memory as a `Vec<u8>` would mean copying
/// it, and deciding to copy is not this crate's decision to make. So the
/// allocation is wrapped instead: it derefs to `[u8]`, and a caller who wants
/// an owned `Vec` can say so.
///
/// # Why not `Vec<u8>` with a custom allocator
///
/// Rust's allocator API is unstable, and pretending `SQLite`'s heap is the
/// global one would be wrong in a way that only shows up as a corrupted heap.
/// One small owning type is the honest version.
pub struct SqlBytes {
    /// Null only when `len` is zero, which `sqlite3_malloc` is permitted to
    /// return for a zero-length request.
    data: Option<NonNull<u8>>,
    len: usize,
}

impl SqlBytes {
    /// Adopts `len` bytes at `data`.
    ///
    /// # Safety
    ///
    /// `data` must come from `SQLite`'s allocator, be `len` bytes long, and
    /// ownership of it must transfer to the new value. A null `data` is only
    /// permitted when `len` is zero.
    #[must_use]
    pub const unsafe fn from_raw(data: *mut u8, len: usize) -> Self {
        Self {
            data: NonNull::new(data),
            len,
        }
    }

    /// Copies `bytes` into a fresh allocation from `SQLite`'s allocator.
    ///
    /// The copy is the point: entry points that take ownership of a buffer --
    /// `sqlite3_deserialize` with `FREEONCLOSE` -- will eventually `sqlite3_free`
    /// it, and only memory from this allocator may be freed that way.
    ///
    /// # Errors
    ///
    /// Returns `SQLITE_NOMEM` when the allocation fails.
    pub fn copy_from_slice(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.is_empty() {
            return Ok(Self { data: None, len: 0 });
        }
        // SAFETY: asks for a definite number of bytes; a null return is the
        // documented out-of-memory signal and is checked immediately.
        let raw = unsafe { ffi::sqlite3_malloc64(bytes.len() as u64) }.cast::<u8>();
        let Some(data) = NonNull::new(raw) else {
            return Err(Error::new(ResultCode::NOMEM));
        };
        // SAFETY: `data` is a fresh allocation of exactly `bytes.len()` bytes,
        // so it is writable and cannot overlap the source.
        unsafe {
            data.as_ptr()
                .copy_from_nonoverlapping(bytes.as_ptr(), bytes.len());
        }
        Ok(Self {
            data: Some(data),
            len: bytes.len(),
        })
    }

    /// Returns the bytes.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        match self.data {
            // SAFETY: `data` is a live allocation of exactly `len` bytes which
            // this value owns and nothing else writes to.
            Some(data) => unsafe { slice::from_raw_parts(data.as_ptr(), self.len) },
            None => &[],
        }
    }

    /// Gives up ownership, returning the pointer and length.
    ///
    /// The caller becomes responsible for `sqlite3_free`.
    #[must_use]
    pub fn into_raw(self) -> (*mut u8, usize) {
        let this = std::mem::ManuallyDrop::new(self);
        (
            this.data.map_or(std::ptr::null_mut(), NonNull::as_ptr),
            this.len,
        )
    }
}

impl Deref for SqlBytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl AsRef<[u8]> for SqlBytes {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl fmt::Debug for SqlBytes {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SqlBytes")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl Drop for SqlBytes {
    fn drop(&mut self) {
        if let Some(data) = self.data {
            // SAFETY: `data` came from SQLite's allocator and this value owns
            // it, so this is the only free.
            unsafe { ffi::sqlite3_free(data.as_ptr().cast()) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_empty_buffer_derefs_to_an_empty_slice() {
        // SAFETY: null with a zero length is the documented empty case.
        let bytes = unsafe { SqlBytes::from_raw(std::ptr::null_mut(), 0) };
        assert!(bytes.is_empty());
        assert_eq!(&*bytes, &[] as &[u8]);
    }

    #[test]
    fn bytes_from_sqlite_deref_and_free() {
        // SAFETY: a four-byte allocation from SQLite's allocator.
        let raw = unsafe { ffi::sqlite3_malloc(4) }.cast::<u8>();
        assert!(!raw.is_null());
        // SAFETY: `raw` is four writable bytes.
        unsafe { raw.copy_from_nonoverlapping(b"abcd".as_ptr(), 4) };

        // SAFETY: adopting exactly that allocation.
        let bytes = unsafe { SqlBytes::from_raw(raw, 4) };
        assert_eq!(&*bytes, b"abcd");
        assert_eq!(bytes.as_ref(), b"abcd");
        // Dropping frees it; running under a sanitizer would catch a mistake.
    }

    #[test]
    fn a_copy_owns_its_own_allocation() {
        let bytes = SqlBytes::copy_from_slice(b"abcd").expect("allocate");
        assert_eq!(&*bytes, b"abcd");
        assert!(SqlBytes::copy_from_slice(b"").expect("allocate").is_empty());
    }

    #[test]
    fn into_raw_gives_up_ownership() {
        // SAFETY: a one-byte allocation from SQLite's allocator.
        let raw = unsafe { ffi::sqlite3_malloc(1) }.cast::<u8>();
        // SAFETY: adopting exactly that allocation.
        let bytes = unsafe { SqlBytes::from_raw(raw, 1) };
        let (pointer, len) = bytes.into_raw();
        assert_eq!(pointer, raw);
        assert_eq!(len, 1);
        // SAFETY: ownership came back to us, so we free it exactly once.
        unsafe { ffi::sqlite3_free(pointer.cast()) };
    }
}
