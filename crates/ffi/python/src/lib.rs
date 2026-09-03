//! The compiled half of the `covalence` Python package.
//!
//! This is the composition layer: it may depend on `covalence-lib-python` and
//! on public Covalence crates, define Python classes and functions, and turn
//! domain errors into exceptions. The dependency only ever points this way —
//! no crate under `crates/lib` or `crates/data` may depend on this one, which
//! is what keeps Python out of the core.
//!
//! One extension module for the whole project, not one per Rust crate. Callers
//! import `covalence`; that package is assembled in `python/covalence`, and
//! this module is the private `covalence._covalence` it re-exports from.
//!
//! Everything here is a thin wrapper. Hashing, encoding, and derivation are
//! implemented once, in the crate being wrapped, and nothing in this crate or
//! in the Python beside it reimplements any of it.

use covalence_lib_python::prelude::*;

mod cas;
mod cbor;
mod classical;
mod hash;
mod hol;
mod lrat;
mod metamath;
mod sat;
mod sexpr;

/// `covalence._covalence`.
#[pymodule]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn _covalence(module: &Bound<'_, PyModule>) -> PyResult<()> {
    // Release wheels carry a Python-specific PEP 440 version. Development
    // builds retain the workspace Cargo version without requiring every Rust
    // crate to adopt the Python release cadence.
    let version = option_env!("COVALENCE_PYTHON_VERSION")
        .filter(|version| !version.is_empty())
        .unwrap_or(env!("CARGO_PKG_VERSION"));
    module.add("__version__", version)?;
    cbor::register(module)?;
    classical::register(module)?;
    hash::register(module)?;
    cas::register(module)?;
    hol::register(module)?;
    sat::register(module)?;
    lrat::register(module)?;
    metamath::register(module)?;
    sexpr::register(module)
}
