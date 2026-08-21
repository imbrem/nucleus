#![allow(unsafe_code)]
//! `SQLite` result codes and errors.

use std::borrow::Cow;
use std::ffi::{CStr, c_int};
use std::fmt;

use covalence_lib_error::snafu::Snafu;

use crate::ffi;

/// An `SQLite` result code, primary or extended.
///
/// The wrapped integer is exactly what the C API returned. Extended codes are
/// preserved; use [`ResultCode::primary`] to narrow one to its primary code.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ResultCode(c_int);

impl ResultCode {
    /// Successful result.
    pub const OK: Self = Self(ffi::SQLITE_OK);
    /// A row of output is available.
    pub const ROW: Self = Self(ffi::SQLITE_ROW);
    /// Execution finished.
    pub const DONE: Self = Self(ffi::SQLITE_DONE);
    /// The library was used incorrectly.
    pub const MISUSE: Self = Self(ffi::SQLITE_MISUSE);
    /// The database file is locked.
    pub const BUSY: Self = Self(ffi::SQLITE_BUSY);
    /// Out of memory.
    pub const NOMEM: Self = Self(ffi::SQLITE_NOMEM);
    /// `SQLITE_MISMATCH`: a value had the wrong storage class.
    pub const MISMATCH: Self = Self(ffi::SQLITE_MISMATCH);

    /// Wraps a raw result code.
    #[must_use]
    pub const fn new(code: c_int) -> Self {
        Self(code)
    }

    /// Returns the raw result code.
    #[must_use]
    pub const fn get(self) -> c_int {
        self.0
    }

    /// Returns the primary result code, discarding any extended bits.
    #[must_use]
    pub const fn primary(self) -> Self {
        Self(self.0 & 0xff)
    }

    /// Reports whether this code is `SQLITE_OK`.
    #[must_use]
    pub const fn is_ok(self) -> bool {
        self.0 == ffi::SQLITE_OK
    }

    /// Converts a code into `Ok(())` or an [`Error`] carrying no message.
    ///
    /// # Errors
    ///
    /// Returns an error for every code other than `SQLITE_OK`.
    pub const fn ok(self) -> Result<(), Error> {
        if self.is_ok() {
            Ok(())
        } else {
            Err(Error::new(self))
        }
    }
}

impl fmt::Display for ResultCode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} ({})", describe(*self, None), self.0)
    }
}

/// The message captured with a failure, or `SQLite`'s own static description
/// of the result code when nothing more specific was available.
///
/// Shared by [`ResultCode`] and [`Error`] so both render a failure the same
/// way: the most specific text there is, followed by the raw code.
fn describe(code: ResultCode, message: Option<&str>) -> Cow<'_, str> {
    match message {
        Some(message) => Cow::Borrowed(message),
        // SAFETY: `sqlite3_errstr` accepts any integer and returns a pointer to
        // a NUL-terminated string held in static storage; it is never freed and
        // is not invalidated by other API calls.
        None => unsafe { CStr::from_ptr(ffi::sqlite3_errstr(code.0)) }.to_string_lossy(),
    }
}

/// An `SQLite` failure: a result code and, when one was available, the
/// connection's error message at the time of the failure.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
// SNAFU names the context selector after the type with `Error` trimmed, which
// leaves nothing to name it with here. The selector stays private either way:
// the constructors below are how an `SQLite` failure is built.
#[snafu(context(suffix(SqliteSnafu)))]
#[snafu(display("{} ({})", describe(*code, message.as_deref()), code.get()))]
pub struct Error {
    code: ResultCode,
    message: Option<Box<str>>,
}

impl Error {
    /// Builds an error from a result code alone.
    #[must_use]
    pub const fn new(code: ResultCode) -> Self {
        Self {
            code,
            message: None,
        }
    }

    /// Builds an error from a result code and a message.
    #[must_use]
    pub fn with_message(code: ResultCode, message: impl Into<Box<str>>) -> Self {
        Self {
            code,
            message: Some(message.into()),
        }
    }

    /// Returns the result code.
    #[must_use]
    pub const fn code(&self) -> ResultCode {
        self.code
    }

    /// Returns the recorded message, if any.
    #[must_use]
    pub fn message(&self) -> Option<&str> {
        self.message.as_deref()
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, ResultCode};

    #[test]
    fn extended_codes_retain_their_primary_code() {
        let extended = ResultCode::new(ResultCode::BUSY.get() | (1 << 8));
        assert_ne!(extended, ResultCode::BUSY);
        assert_eq!(extended.primary(), ResultCode::BUSY);
    }

    #[test]
    fn codes_describe_themselves() {
        assert!(ResultCode::OK.is_ok());
        assert!(ResultCode::BUSY.to_string().contains("locked"));
    }

    #[test]
    fn messages_replace_the_generic_description() {
        let plain = Error::new(ResultCode::MISUSE);
        assert_eq!(plain.message(), None);
        let described = Error::with_message(ResultCode::MISUSE, "no such column: x");
        assert_eq!(described.message(), Some("no such column: x"));
        assert!(described.to_string().starts_with("no such column: x"));
    }
}
