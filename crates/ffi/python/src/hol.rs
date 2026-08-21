//! `covalence-logic-hol` at the Python boundary.
//!
//! This module only owns opaque wrappers. Admission and state transitions stay
//! in `covalence-logic-hol`; no logical check is repeated here.

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_hol::{Error, Kind, Tm, Ty, dense};

create_exception!(
    covalence,
    HolError,
    PyValueError,
    "An HOL kernel operation was rejected."
);

fn rejection(error: &Error) -> PyErr {
    HolError::new_err(error.to_string())
}

/// An opaque, portable HOL type handle.
#[pyclass(frozen, module = "covalence.logic.hol", name = "Ty")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[expect(
    dead_code,
    reason = "the opaque handle intentionally exposes no type operations yet"
)]
pub struct PyTy(Ty);

/// An opaque, portable HOL kind handle.
#[pyclass(frozen, module = "covalence.logic.hol", name = "Kind")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[expect(
    dead_code,
    reason = "the opaque handle intentionally exposes no kind operations yet"
)]
pub struct PyKind(Kind);

/// An opaque, portable HOL term handle.
#[pyclass(frozen, module = "covalence.logic.hol", name = "Tm")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[expect(
    dead_code,
    reason = "the opaque handle intentionally exposes no term operations yet"
)]
pub struct PyTm(Tm);

/// An owning wrapper over an admitted HOL arena.
///
/// The compiled class has a distinct private name because the extension also
/// contains the LRAT kernel. `covalence.logic.hol` exports it as `Kernel`.
#[pyclass(module = "covalence.logic.hol", name = "HolKernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel(dense::Kernel);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    /// Construct an empty admitted arena.
    #[staticmethod]
    fn empty() -> Self {
        Self(dense::Kernel::empty())
    }

    /// Insert and return a Boolean type handle.
    fn bool_ty(&mut self) -> PyResult<PyTy> {
        self.0
            .bool_ty()
            .map(PyTy)
            .map_err(|error| rejection(&error))
    }

    /// Insert and return the kind `Star`.
    fn star(&mut self) -> PyResult<PyKind> {
        self.0.star().map(PyKind).map_err(|error| rejection(&error))
    }

    /// Insert and return a Boolean constant handle.
    fn bool_const(&mut self, value: bool) -> PyResult<PyTm> {
        self.0
            .bool_const(value)
            .map(PyTm)
            .map_err(|error| rejection(&error))
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyKernel>()?;
    module.add_class::<PyKind>()?;
    module.add_class::<PyTy>()?;
    module.add_class::<PyTm>()?;
    let error = PyType::new::<HolError>(module.py());
    error.setattr("__module__", "covalence.logic.hol")?;
    module.add("HolError", error)
}
