//! A [`Cas`] provided by the WASI host.
//!
//! In a browser there are no sockets, so the shell reaches its store the way a
//! wasm guest reaches anything: through imports. These four are the
//! `covalence:cas/store` interface of the WIT contract, in the shape the
//! `wasm32-wasip1` ABI can express — a resource handle plus operations on it.
//!
//! # Handles, again
//!
//! `open` resolves an address once and returns a handle; reads name the
//! handle. The host holds the object for as long as the handle lives, which is
//! the same guarantee the socket transport carries natively: a `.forget` while
//! this shell has a database open cannot break it.
//!
//! # Trust
//!
//! The host is not trusted by this guest and does not need to be, because this
//! guest is the shell. It is the *host* that is protected here: the shell can
//! ask for objects the host chose to serve, and can do nothing else. There is
//! no write operation, no enumeration, and no path out of the sandbox.

use std::ops::Range;

use bytes::Bytes;
use covalence_data_cas::{Cas, CasObject};
use covalence_lib_hash::O256;

/// Sentinel returned by `cas_open` when the address does not resolve.
const ABSENT: i64 = -1;

#[allow(unsafe_code, reason = "declares the host's CAS imports")]
#[link(wasm_import_module = "covalence:cas")]
unsafe extern "C" {
    /// Opens the 32-byte address at `address`.
    ///
    /// Returns a non-negative handle, [`ABSENT`] when it does not resolve, or
    /// any other negative value on failure.
    fn cas_open(address: *const u8) -> i64;

    /// Returns the length of an open handle, or a negative value on failure.
    fn cas_length(handle: i64) -> i64;

    /// Reads `len` bytes from `offset` into `out`.
    ///
    /// Returns the number of bytes written, or a negative value on failure.
    fn cas_read(handle: i64, offset: u64, len: u32, out: *mut u8) -> i32;

    /// Releases a handle.
    fn cas_close(handle: i64);
}

/// Failure to read from the host's store.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostError {
    /// The host refused an operation.
    Refused,
    /// The host returned fewer bytes than were asked for.
    ///
    /// A short read must not become a short page: `SQLite` would read the
    /// difference as zeroes and see a corrupt database.
    ShortRead {
        /// Bytes requested.
        expected: u64,
        /// Bytes the host produced.
        actual: usize,
    },
    /// The requested range does not lie inside the object.
    InvalidRange {
        /// Requested inclusive start.
        start: u64,
        /// Requested exclusive end.
        end: u64,
        /// Length of the object.
        len: u64,
    },
}

impl std::fmt::Display for HostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Refused => formatter.write_str("the host refused the request"),
            Self::ShortRead { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected} bytes, host returned {actual}"
                )
            }
            Self::InvalidRange { start, end, len } => write!(
                formatter,
                "range {start}..{end} lies outside an object of {len} bytes"
            ),
        }
    }
}

impl std::error::Error for HostError {}

/// The store the host is serving to this guest.
#[derive(Clone, Copy, Debug, Default)]
pub struct HostCas;

/// An object the host is holding open for this guest.
#[derive(Debug)]
pub struct HostObject {
    handle: i64,
    len: u64,
}

impl Cas for HostCas {
    type Error = HostError;
    type Object = HostObject;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        // SAFETY: `address` is 32 bytes and lives for the duration of the
        // call, which is what the host reads.
        #[allow(unsafe_code, reason = "calls the host's CAS import")]
        let handle = unsafe { cas_open(address.as_bytes().as_ptr()) };
        if handle == ABSENT {
            return Ok(None);
        }
        if handle < 0 {
            return Err(HostError::Refused);
        }
        // SAFETY: `handle` was just returned as valid by the host.
        #[allow(unsafe_code, reason = "calls the host's CAS import")]
        let len = unsafe { cas_length(handle) };
        if len < 0 {
            // SAFETY: releasing a handle the host gave us.
            #[allow(unsafe_code, reason = "calls the host's CAS import")]
            unsafe {
                cas_close(handle);
            }
            return Err(HostError::Refused);
        }
        Ok(Some(HostObject {
            handle,
            len: len.unsigned_abs(),
        }))
    }
}

impl CasObject for HostObject {
    type Error = HostError;

    fn len(&self) -> u64 {
        self.len
    }

    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
        if range.start > range.end || range.end > self.len {
            return Err(HostError::InvalidRange {
                start: range.start,
                end: range.end,
                len: self.len,
            });
        }
        let wanted = range.end - range.start;
        let Ok(capacity) = usize::try_from(wanted) else {
            return Err(HostError::Refused);
        };
        let Ok(length) = u32::try_from(wanted) else {
            return Err(HostError::Refused);
        };

        let mut buffer = vec![0u8; capacity];
        // SAFETY: `buffer` has exactly `length` writable bytes and the handle
        // is one the host gave us and has not been closed.
        #[allow(unsafe_code, reason = "calls the host's CAS import")]
        let produced = unsafe { cas_read(self.handle, range.start, length, buffer.as_mut_ptr()) };
        if produced < 0 {
            return Err(HostError::Refused);
        }
        let produced = produced.unsigned_abs() as usize;
        if produced as u64 != wanted {
            return Err(HostError::ShortRead {
                expected: wanted,
                actual: produced,
            });
        }
        Ok(Bytes::from(buffer))
    }
}

impl Drop for HostObject {
    fn drop(&mut self) {
        // SAFETY: releasing a handle the host gave us, exactly once.
        #[allow(unsafe_code, reason = "calls the host's CAS import")]
        unsafe {
            cas_close(self.handle);
        }
    }
}
