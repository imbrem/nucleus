//! `covalence-lib-hash` at the Python boundary.
//!
//! Every namespace gets its own Python class, and all of them derive from
//! `Obj`. They wrap 20 or 32 bytes and would be interchangeable if they were
//! one type, which is exactly what the Rust API spends a type parameter to
//! prevent: a Git object name and a Covalence object are not the same thing
//! because their widths agree. `Obj` carries what follows from having bytes —
//! the encodings, ordering, hashing, the value protocol — and the subclasses
//! carry the namespace, so `isinstance(value, Obj)` is the way to ask the
//! general question while equality between two namespaces stays `False`.
//!
//! Construction is as permissive as the Rust constructors and no more. Raw bytes
//! and canonical hex name a value without checking that anything ever hashed to
//! it, and the classes say so rather than implying validation they do not do.
//! What they do enforce is the width and the encoding.
//!
//! Hashing releases the GIL. The input is either an immutable `bytes` object
//! borrowed in place or a copy this crate owns, so nothing can change underneath
//! the hasher while another thread runs.

// Both of these describe `PyO3`'s calling convention rather than a choice made
// here. Extraction produces an owned `Bytes`, so a binding takes one by value
// and reads it; and a `#[pymethods]` method borrows from the Python object that
// owns it, so a `to_*` conversion cannot take `self` by value however cheap the
// copy would be.
#![allow(clippy::needless_pass_by_value, clippy::wrong_self_convention)]

use std::{
    fmt::Write as _,
    hash::{DefaultHasher, Hash, Hasher},
};

use covalence_lib_hash::{
    Blake3, COV, COV_ROOT, Cov, CtxKey, CtxKeyNamespace, Git, O256, Obj, ParseBase64Error,
    ParseHexError, RootedNamespace, Sha1, Sha256, git_blob, git_object,
};
use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    IntoPyObject, PyClassInitializer, basic::CompareOp, types::PyBytes, types::PyType,
};

create_exception!(
    covalence,
    InvalidLengthError,
    PyValueError,
    "A value had the wrong number of bytes or encoded characters."
);
create_exception!(
    covalence,
    InvalidHexError,
    PyValueError,
    "A hexadecimal string contained something that is not a hexadecimal digit."
);
create_exception!(
    covalence,
    InvalidBase64Error,
    PyValueError,
    "A Base64 string was outside the alphabet, mispadded, or non-canonical."
);

/// Reports the width mistake separately from the content mistake, because they
/// are different things for a caller to have got wrong.
fn hex_error(error: ParseHexError) -> PyErr {
    match error {
        ParseHexError::InvalidLength { .. } => InvalidLengthError::new_err(error.to_string()),
        ParseHexError::InvalidDigit { .. } => InvalidHexError::new_err(error.to_string()),
    }
}

fn base64_error(error: ParseBase64Error) -> PyErr {
    match error {
        ParseBase64Error::InvalidLength { .. } => InvalidLengthError::new_err(error.to_string()),
        _ => InvalidBase64Error::new_err(error.to_string()),
    }
}

fn exact<const BYTES: usize>(data: &[u8]) -> PyResult<[u8; BYTES]> {
    data.try_into().map_err(|_| {
        InvalidLengthError::new_err(format!("expected {BYTES} bytes, found {}", data.len()))
    })
}

/// A fixed-width Covalence identifier, of no particular namespace.
///
/// Holds the bytes and everything that follows from having them. What it
/// deliberately does not hold is a way to make one: a value with no namespace
/// is the thing this API exists to rule out, so `Obj` has no constructor and
/// only its subclasses can be instantiated. It is useful as a type to name —
/// `isinstance(value, Obj)`, or an annotation covering every namespace at once.
///
/// Ordering is bytewise and hashing agrees with equality, but both stop at the
/// namespace boundary: comparing two namespaces is `False`, and ordering them
/// against each other raises `TypeError`, however their bytes compare.
#[pyclass(subclass, frozen, module = "covalence.hash", name = "Obj")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyObj {
    /// Wide enough for every namespace, so a value costs no allocation.
    bytes: [u8; 32],
    width: usize,
}

impl PyObj {
    fn new(bytes: &[u8]) -> Self {
        let mut buffer = [0; 32];
        buffer[..bytes.len()].copy_from_slice(bytes);
        Self {
            bytes: buffer,
            width: bytes.len(),
        }
    }

    fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.width]
    }

    /// The bytes at the width the calling namespace declares.
    ///
    /// Infallible in practice: a value only ever reaches this class through a
    /// subclass constructor that has already checked the width.
    fn array<const BYTES: usize>(&self) -> [u8; BYTES] {
        self.as_slice()
            .try_into()
            .expect("a namespace's values have its width")
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyObj {
    /// Lowercase hexadecimal.
    fn hex(&self) -> String {
        let mut text = String::with_capacity(self.width * 2);
        for byte in self.as_slice() {
            let _ = write!(text, "{byte:02x}");
        }
        text
    }

    fn __bytes__<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, self.as_slice())
    }

    fn __len__(&self) -> usize {
        self.width
    }

    fn __str__(&self) -> String {
        self.hex()
    }

    fn __repr__(slf: &Bound<'_, Self>) -> PyResult<String> {
        let name = slf.get_type().name()?;
        Ok(format!("{name}.from_hex('{}')", slf.get().hex()))
    }

    /// Compares within a namespace and refuses to compare across one.
    ///
    /// Returning `NotImplemented` rather than `False` for a mismatch is what
    /// makes `==` false and `<` a `TypeError`, which is the asymmetry that is
    /// wanted: asking whether two names are the same value is reasonable, and
    /// asking which of them sorts first is not.
    fn __richcmp__(
        slf: &Bound<'_, Self>,
        other: &Bound<'_, PyAny>,
        op: CompareOp,
        python: Python<'_>,
    ) -> PyResult<Py<PyAny>> {
        if !other.get_type().is(slf.get_type()) {
            return Ok(python.NotImplemented());
        }
        let this = slf.get().as_slice();
        let that = other.cast::<Self>()?.get().as_slice();
        Ok(op
            .matches(this.cmp(that))
            .into_pyobject(python)?
            .to_owned()
            .into_any()
            .unbind())
    }

    fn __hash__(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.as_slice().hash(&mut hasher);
        hasher.finish()
    }
}

/// Defines the Python class for one namespace.
///
/// The shared half is on `Obj`. What each namespace repeats is only what it
/// cannot share: its width, and the constructors, which have to return the
/// namespace being constructed. The rest — hashing, derivation, the conversions
/// a namespace actually has — is passed in, because it differs for every one of
/// them and inventing a uniform version is how the distinction gets lost.
macro_rules! object {
    (
        $wrapper:ident, $name:literal, $namespace:ty, $bytes:literal, $doc:literal,
        { $($extra:tt)* }
    ) => {
        #[doc = $doc]
        #[pyclass(
            frozen,
            extends = PyObj,
            module = "covalence.hash",
            name = $name,
            crate = "covalence_lib_python::pyo3"
        )]
        pub struct $wrapper;

        impl $wrapper {
            /// Wraps a Rust value as a new Python object of this class.
            fn wrap(python: Python<'_>, value: Obj<$namespace>) -> PyResult<Py<Self>> {
                Py::new(python, Self::initializer(PyObj::new(value.as_ref())))
            }

            fn initializer(base: PyObj) -> PyClassInitializer<Self> {
                PyClassInitializer::from(base).add_subclass(Self)
            }

            /// The Rust value behind a Python object of this class.
            ///
            /// Unused by namespaces that only hash and compare.
            #[allow(dead_code)]
            fn value(slf: &PyRef<'_, Self>) -> Obj<$namespace> {
                Obj::from_array(slf.as_super().array::<$bytes>())
            }
        }

        #[pymethods]
        #[pyo3(crate = "covalence_lib_python::pyo3")]
        impl $wrapper {
            /// Width in bytes.
            #[classattr]
            const BYTES: usize = $bytes;

            /// Names a value from its exact bytes, without validating that
            /// anything hashed to it.
            #[new]
            fn new(data: Bytes) -> PyResult<PyClassInitializer<Self>> {
                let bytes = exact::<$bytes>(data.as_slice())?;
                Ok(Self::initializer(PyObj::new(&bytes)))
            }

            /// Decodes exact-width lowercase or uppercase hexadecimal.
            #[staticmethod]
            fn from_hex(python: Python<'_>, text: &str) -> PyResult<Py<Self>> {
                let value = text.parse::<Obj<$namespace>>().map_err(hex_error)?;
                Self::wrap(python, value)
            }

            /// Decodes canonical padded standard Base64.
            #[staticmethod]
            fn from_base64(python: Python<'_>, text: &str) -> PyResult<Py<Self>> {
                let value = Obj::<$namespace>::from_base64::<$bytes>(text)
                    .map_err(base64_error)?;
                Self::wrap(python, value)
            }

            $($extra)*
        }
    };
}

object!(
    PyO256,
    "O256",
    Cov,
    32,
    "A standard Covalence 256-bit object.\n\
     \n\
     The interoperable namespace: content hashing embeds BLAKE3 into it, and \
     the tag hierarchy is built in it.",
    {
        /// BLAKE3 of `data`, in the Covalence namespace.
        #[staticmethod]
        fn hash(python: Python<'_>, data: Bytes) -> PyResult<Py<Self>> {
            Self::wrap(python, python.detach(|| O256::from_bytes(data.as_slice())))
        }

        /// Keyed BLAKE3 of `data` under another object.
        #[staticmethod]
        fn keyed(python: Python<'_>, key: PyRef<'_, Self>, data: Bytes) -> PyResult<Py<Self>> {
            let key = Self::value(&key);
            Self::wrap(
                python,
                python.detach(|| O256::with_key(&key, data.as_slice())),
            )
        }

        /// BLAKE3 `derive_key` of `data` under a context string.
        ///
        /// Equivalent to deriving a `ContextKey` from `context` and hashing
        /// under it, and the reason a context is a human-readable, versioned
        /// string rather than a value anyone can pick.
        #[staticmethod]
        fn derive_key(python: Python<'_>, context: &str, data: Bytes) -> PyResult<Py<Self>> {
            // `context` borrows from Python, so it is copied out before the GIL
            // is released rather than captured by the closure.
            let context = context.to_owned();
            Self::wrap(
                python,
                python.detach(|| O256::with_key(context.as_str(), data.as_slice())),
            )
        }

        /// Hashes `data` under a precomputed context key.
        #[staticmethod]
        fn with_context(
            python: Python<'_>,
            key: PyRef<'_, PyContextKey>,
            data: Bytes,
        ) -> PyResult<Py<Self>> {
            let key = PyContextKey::value(&key);
            Self::wrap(
                python,
                python.detach(|| O256::with_ctx(&key, data.as_slice())),
            )
        }

        /// The root of the standard Covalence hierarchy.
        #[staticmethod]
        fn root(python: Python<'_>) -> PyResult<Py<Self>> {
            Self::wrap(python, O256::root())
        }

        /// Derives the child named `data` below this object.
        fn tag(slf: PyRef<'_, Self>, python: Python<'_>, data: Bytes) -> PyResult<Py<Self>> {
            let parent = Self::value(&slf);
            Self::wrap(python, python.detach(|| parent.tag(data.as_slice())))
        }
    }
);

object!(
    PyBlake3,
    "Blake3",
    Blake3,
    32,
    "An unkeyed BLAKE3 digest.\n\
     \n\
     Algorithm-specific, and deliberately supports neither random construction \
     nor self-tagging.",
    {
        /// BLAKE3 of `data`.
        #[staticmethod]
        fn hash(python: Python<'_>, data: Bytes) -> PyResult<Py<Self>> {
            Self::wrap(
                python,
                python.detach(|| Obj::<Blake3>::from_bytes(data.as_slice())),
            )
        }

        /// Embeds this digest into the Covalence namespace.
        ///
        /// Covalence currently uses BLAKE3 as its content-hash embedding, so
        /// the bytes are unchanged. The conversion exists in this direction
        /// only: not every Covalence object is a BLAKE3 digest.
        fn to_o256(slf: PyRef<'_, Self>, python: Python<'_>) -> PyResult<Py<PyO256>> {
            PyO256::wrap(python, Self::value(&slf).into_o256())
        }
    }
);

object!(PySha256, "Sha256", Sha256, 32, "A SHA-256 digest.", {
    /// SHA-256 of `data`.
    #[staticmethod]
    fn hash(python: Python<'_>, data: Bytes) -> PyResult<Py<Self>> {
        Self::wrap(
            python,
            python.detach(|| Obj::<Sha256>::from_bytes(data.as_slice())),
        )
    }
});

object!(
    PyContextKey,
    "ContextKey",
    CtxKeyNamespace,
    32,
    "A BLAKE3 derive-key context key.\n\
     \n\
     Anchors a hierarchy. Independently issued ones stay practically disjoint, \
     which is what lets hierarchies be mounted together without coordinating.",
    {
        /// Derives a context key from a human-readable context string.
        #[staticmethod]
        fn derive(python: Python<'_>, context: &str) -> PyResult<Py<Self>> {
            Self::wrap(python, CtxKey::derive(context))
        }

        /// The empty-string root below this context key.
        fn root(slf: PyRef<'_, Self>, python: Python<'_>) -> PyResult<Py<PyO256>> {
            PyO256::wrap(python, Self::value(&slf).root())
        }

        /// Derives the child named `data` below this context key.
        fn tag(slf: PyRef<'_, Self>, python: Python<'_>, data: Bytes) -> PyResult<Py<PyO256>> {
            let context = Self::value(&slf);
            PyO256::wrap(python, python.detach(|| context.tag(data.as_slice())))
        }
    }
);

object!(
    PySha1,
    "Sha1",
    Sha1,
    20,
    "A raw SHA-1 digest.\n\
     \n\
     Unframed: this is SHA-1 of the bytes given, which is not how Git names an \
     object. See `git_blob`.",
    {
        /// SHA-1 of `data`.
        #[staticmethod]
        fn hash(python: Python<'_>, data: Bytes) -> PyResult<Py<Self>> {
            Self::wrap(
                python,
                python.detach(|| Obj::<Sha1>::from_bytes(data.as_slice())),
            )
        }

        /// Reinterprets this digest as a Git object name.
        fn to_git(slf: PyRef<'_, Self>, python: Python<'_>) -> PyResult<Py<PyGitHash>> {
            PyGitHash::wrap(python, Self::value(&slf).into_git())
        }
    }
);

object!(
    PyGitHash,
    "GitHash",
    Git,
    20,
    "A traditional Git SHA-1 object name.\n\
     \n\
     Content-derived, and so cannot be generated from randomness.",
    {
        /// Reinterprets this name as its raw SHA-1 digest.
        fn to_sha1(slf: PyRef<'_, Self>, python: Python<'_>) -> PyResult<Py<PySha1>> {
            PySha1::wrap(python, Self::value(&slf).into_sha1())
        }
    }
);

/// Names a Git object of type `object_type` holding `data`.
///
/// Git hashes a header — the type, the length, and a NUL — before the content,
/// so this is not SHA-1 of `data` and the two disagree for every input.
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "git_object")]
fn git_object_name(python: Python<'_>, object_type: &str, data: Bytes) -> PyResult<Py<PyGitHash>> {
    let object_type = object_type.to_owned();
    PyGitHash::wrap(
        python,
        python.detach(|| git_object(&object_type, data.as_slice())),
    )
}

/// Names the Git blob holding `data`, as `git hash-object` would.
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "git_blob")]
fn git_blob_name(python: Python<'_>, data: Bytes) -> PyResult<Py<PyGitHash>> {
    PyGitHash::wrap(python, python.detach(|| git_blob(data.as_slice())))
}

/// Adds the hash API to the extension module.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyObj>()?;
    module.add_class::<PyO256>()?;
    module.add_class::<PyBlake3>()?;
    module.add_class::<PySha256>()?;
    module.add_class::<PyContextKey>()?;
    module.add_class::<PySha1>()?;
    module.add_class::<PyGitHash>()?;

    let python = module.py();
    for (name, exception) in [
        (
            "InvalidLengthError",
            PyType::new::<InvalidLengthError>(python),
        ),
        ("InvalidHexError", PyType::new::<InvalidHexError>(python)),
        (
            "InvalidBase64Error",
            PyType::new::<InvalidBase64Error>(python),
        ),
    ] {
        // `create_exception!` accepts a Rust module identifier rather than a
        // dotted Python path. Publish the public location explicitly: the
        // native module is private and `covalence` no longer exports these.
        exception.setattr("__module__", "covalence.hash")?;
        module.add(name, exception)?;
    }

    for function in [
        wrap_pyfunction!(git_object_name, module)?,
        wrap_pyfunction!(git_blob_name, module)?,
    ] {
        function.setattr("__module__", "covalence.hash")?;
        module.add_function(function)?;
    }

    // The checked-in roots of the standard hierarchy. `COV_ROOT_CTX_KEY` is
    // published alongside the key derived from it, so that the derivation can
    // be reproduced rather than taken on trust.
    module.add("COV", PyContextKey::wrap(python, COV)?)?;
    module.add("COV_ROOT", PyO256::wrap(python, COV_ROOT)?)?;
    module.add("COV_ROOT_CTX_KEY", <Cov as RootedNamespace>::ROOT_CTX_KEY)?;
    Ok(())
}
