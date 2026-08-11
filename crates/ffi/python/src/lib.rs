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
//! The public API arrives in later changes. What is here now is the module
//! itself and the metadata needed to tell one build from another.

use covalence_lib_python::prelude::*;

/// `covalence._covalence`.
#[pymodule]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn _covalence(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add("__version__", env!("CARGO_PKG_VERSION"))
}
