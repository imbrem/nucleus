//! `SQLite` values.

use std::ffi::c_int;
use std::str;

use crate::ffi;

/// One of the five storage classes an `SQLite` value can have.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueType {
    /// `SQLITE_NULL`.
    Null,
    /// `SQLITE_INTEGER`.
    Integer,
    /// `SQLITE_FLOAT`.
    Real,
    /// `SQLITE_TEXT`.
    Text,
    /// `SQLITE_BLOB`.
    Blob,
}

impl ValueType {
    /// Reads a storage class from `sqlite3_column_type`.
    ///
    /// Returns `None` for a code `SQLite` is not documented to produce.
    #[must_use]
    pub const fn from_raw(code: c_int) -> Option<Self> {
        match code {
            ffi::SQLITE_NULL => Some(Self::Null),
            ffi::SQLITE_INTEGER => Some(Self::Integer),
            ffi::SQLITE_FLOAT => Some(Self::Real),
            ffi::SQLITE_TEXT => Some(Self::Text),
            ffi::SQLITE_BLOB => Some(Self::Blob),
            _ => None,
        }
    }
}

/// A borrowed column value.
///
/// The borrow lasts until the statement is stepped, reset, or finalized, which
/// is exactly the lifetime `SQLite` guarantees for the pointers behind
/// `sqlite3_column_text` and `sqlite3_column_blob`.
///
/// A value is produced by reading the column's storage class first and then
/// calling only the matching accessor. No accessor is ever asked to convert, so
/// `SQLite` never reallocates a value out from under a pointer this crate has
/// already handed out. Coercion is a policy decision and belongs above this
/// crate.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ValueRef<'a> {
    /// `NULL`.
    Null,
    /// A 64-bit integer.
    Integer(i64),
    /// A 64-bit float.
    Real(f64),
    /// UTF-8 text. `SQLite` does not validate encodings on read, so this is
    /// exposed as bytes; see [`ValueRef::as_str`].
    Text(&'a [u8]),
    /// A byte string.
    Blob(&'a [u8]),
}

impl<'a> ValueRef<'a> {
    /// Returns the value's storage class.
    #[must_use]
    pub const fn value_type(&self) -> ValueType {
        match self {
            Self::Null => ValueType::Null,
            Self::Integer(_) => ValueType::Integer,
            Self::Real(_) => ValueType::Real,
            Self::Text(_) => ValueType::Text,
            Self::Blob(_) => ValueType::Blob,
        }
    }

    /// Returns the integer in this value, if it is one.
    #[must_use]
    pub const fn as_integer(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the float in this value, if it is one.
    #[must_use]
    pub const fn as_real(&self) -> Option<f64> {
        match self {
            Self::Real(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the bytes of a text or blob value.
    #[must_use]
    pub const fn as_bytes(&self) -> Option<&'a [u8]> {
        match self {
            Self::Text(bytes) | Self::Blob(bytes) => Some(bytes),
            _ => None,
        }
    }

    /// Returns a text value decoded as UTF-8.
    ///
    /// Returns `None` when the value is not text or is not valid UTF-8. A
    /// database written by this crate always round-trips, since
    /// [`Statement::bind_text`](crate::Statement::bind_text) takes `&str`.
    #[must_use]
    pub fn as_str(&self) -> Option<&'a str> {
        match self {
            Self::Text(bytes) => str::from_utf8(bytes).ok(),
            _ => None,
        }
    }

    /// Reports whether the value is `NULL`.
    #[must_use]
    pub const fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }
}

#[cfg(test)]
mod tests {
    use super::{ValueRef, ValueType};

    #[test]
    fn a_value_reports_its_storage_class() {
        assert_eq!(ValueRef::Null.value_type(), ValueType::Null);
        assert_eq!(ValueRef::Integer(1).value_type(), ValueType::Integer);
        assert_eq!(ValueRef::Real(1.0).value_type(), ValueType::Real);
        assert_eq!(ValueRef::Text(b"a").value_type(), ValueType::Text);
        assert_eq!(ValueRef::Blob(b"a").value_type(), ValueType::Blob);
    }

    #[test]
    fn accessors_do_not_coerce_between_storage_classes() {
        assert_eq!(ValueRef::Integer(7).as_integer(), Some(7));
        assert_eq!(ValueRef::Real(7.0).as_integer(), None);
        assert_eq!(ValueRef::Text(b"7").as_integer(), None);
        assert_eq!(ValueRef::Blob(b"ok").as_str(), None);
        assert_eq!(ValueRef::Text(b"ok").as_str(), Some("ok"));
        assert_eq!(ValueRef::Text(&[0xff]).as_str(), None);
    }
}
