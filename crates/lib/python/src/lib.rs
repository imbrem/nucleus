//! `PyO3` support shared by Covalence's Python bindings.
//!
//! This crate owns the `PyO3` dependency and the conventions that go with it. It
//! deliberately knows nothing about hashes, stores, or proofs: domain types and
//! the Python classes wrapping them belong in the binding crate, so that adding
//! a Python API never turns a core crate into a Python dependent.
//!
//! Binding crates depend on this rather than on `PyO3` directly, and reach `PyO3`
//! through [`pyo3`]. Because the derive macros generate paths to the crate they
//! were expanded from, each annotated item names the re-export:
//!
//! ```
//! use covalence_lib_python::pyo3::prelude::*;
//!
//! #[pyfunction]
//! #[pyo3(crate = "covalence_lib_python::pyo3")]
//! fn answer() -> u32 {
//!     42
//! }
//! ```
//!
//! # Supported Python and `PyO3`
//!
//! `PyO3` is pinned to 0.29 and built against the stable ABI from Python 3.11
//! (`abi3-py311`). One extension module therefore loads into every interpreter
//! from 3.11 onwards, and the supported range widens by relaxing that feature
//! rather than by shipping one artefact per interpreter version.
//!
//! `extension-module` is *not* enabled by default. A library built with it
//! leaves every Python symbol undefined, which is correct for a shared object
//! loaded into an interpreter and fatal for an executable that has to link.
//! Since `cargo test` and Buck both produce executables, the feature is
//! selected only by the wheel build; ordinary builds link an interpreter and
//! can run their tests.
//!
//! # Ownership and the GIL
//!
//! A `Python<'py>` token proves the current thread holds the GIL, and every
//! `Bound<'py, T>` borrows from it. Neither may be stored in a Rust value that
//! outlives the call that received it; use `Py<T>` for anything long-lived and
//! bind it again under a fresh token.
//!
//! Prefer taking `&Bound<'py, T>` over `Py<T>` in function signatures. The
//! bound form already carries the token, so it neither re-acquires the GIL nor
//! forces a reference-count bump on entry.
//!
//! # Thread safety
//!
//! Covalence's Python classes wrap values that are `Copy`, `Send`, and `Sync`,
//! so they are declared immutable and hold no interior mutability. That is what
//! makes them safe under free-threaded interpreters, and it is the property to
//! preserve: a `#[pyclass]` holding a `RefCell`, an open handle, or anything
//! else with shared mutable state needs an explicit locking story before it is
//! exposed.
//!
//! Release the GIL with `Python::detach` around work that neither touches
//! Python objects nor is over in microseconds — hashing a large buffer, say.
//!
//! # Errors
//!
//! Domain errors convert to Python exceptions at the boundary and nowhere else:
//! a binding function returns [`PyResult`](pyo3::PyResult), and the `From` impl
//! that produces the `PyErr` lives in the binding crate, never in the crate
//! that defines the error. Choose the exception by what the caller did wrong —
//! malformed input is a `ValueError`, a wrong type is a `TypeError` — and
//! reserve module-specific exception classes for distinctions a caller would
//! plausibly branch on.
//!
//! Panics need no handling of their own. `PyO3` catches unwinding at the boundary
//! and raises `pyo3_runtime.PanicException`, so a panic surfaces as an
//! exception rather than as an aborted interpreter.

pub use pyo3;

mod bytes;

pub use bytes::Bytes;

/// Exception types Covalence's bindings raise.
///
/// A curated re-export rather than all of [`pyo3::exceptions`]: the set of
/// exceptions the bindings are allowed to raise is a policy decision, and
/// keeping it here is what makes that policy reviewable in one place.
pub mod exceptions {
    pub use pyo3::exceptions::{PyTypeError, PyValueError};

    /// Declares a module-specific exception class.
    ///
    /// Re-exported so binding crates can define their own exception hierarchy
    /// without naming `PyO3`.
    pub use pyo3::create_exception;
}

/// The imports a binding crate needs.
pub mod prelude {
    pub use pyo3::prelude::*;

    pub use crate::Bytes;
    pub use crate::exceptions::{PyTypeError, PyValueError};
}
