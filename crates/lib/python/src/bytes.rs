//! Byte-buffer input at the Python boundary.

use std::{fmt, ops::Deref};

use pyo3::{
    Borrowed, FromPyObject, PyAny, PyErr, PyResult,
    buffer::PyBuffer,
    exceptions::PyTypeError,
    pybacked::PyBackedBytes,
    types::{PyAnyMethods, PyTypeMethods},
};

/// Bytes borrowed from, or copied out of, a Python object.
///
/// Accepts `bytes`, `bytearray`, and anything else exporting the buffer
/// protocol as a contiguous run of bytes — `memoryview`, `array.array('B')`,
/// and `NumPy`'s `uint8` arrays among them.
///
/// `bytes` is borrowed rather than copied: the immutable object is kept alive
/// for as long as the value is, and its buffer is read in place. Every other
/// source is copied, because nothing else guarantees the bytes will not be
/// mutated while Rust is reading them.
///
/// `str` is rejected. Python's own hashing APIs reject it too, and accepting it
/// would mean silently choosing an encoding on the caller's behalf.
pub struct Bytes(Repr);

enum Repr {
    /// Backed by the original object, which is kept alive by this value.
    Borrowed(PyBackedBytes),
    /// Copied out of a buffer that could otherwise change under us.
    Copied(Vec<u8>),
}

impl Bytes {
    /// Borrows the bytes.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        match &self.0 {
            Repr::Borrowed(bytes) => bytes,
            Repr::Copied(bytes) => bytes,
        }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl fmt::Debug for Bytes {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Bytes")
            .field("len", &self.as_slice().len())
            .finish()
    }
}

impl<'a, 'py> FromPyObject<'a, 'py> for Bytes {
    type Error = PyErr;

    fn extract(object: Borrowed<'a, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bytes) = PyBackedBytes::extract(object) {
            return Ok(Self(Repr::Borrowed(bytes)));
        }

        // The buffer protocol is the general case, and also the one that can
        // fail for reasons worth reporting: a non-contiguous or non-byte
        // buffer is a different mistake from passing an `int`.
        let buffer = PyBuffer::<u8>::get(&object).map_err(|_| {
            PyTypeError::new_err(format!(
                "expected bytes, bytearray, or an object supporting the buffer \
                 protocol, found {}",
                type_name(object)
            ))
        })?;
        if !buffer.is_c_contiguous() {
            return Err(PyTypeError::new_err(
                "expected a contiguous buffer of bytes",
            ));
        }
        Ok(Self(Repr::Copied(buffer.to_vec(object.py())?)))
    }
}

fn type_name(object: Borrowed<'_, '_, PyAny>) -> String {
    object
        .get_type()
        .name()
        .map_or_else(|_| "an unknown type".to_owned(), |name| name.to_string())
}
