//! `covalence-logic-hol` at the Python boundary.
//!
//! This module only owns opaque wrappers. Admission and state transitions stay
//! in `covalence-logic-hol`; no logical check is repeated here.

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_hol::{Error, Kernel, Tm, Ty};

create_exception!(
    covalence,
    HolError,
    PyValueError,
    "An HOL kernel operation was rejected."
);

fn rejection(error: Error) -> PyErr {
    HolError::new_err(error.to_string())
}

/// An opaque, portable HOL type handle.
#[pyclass(frozen, module = "covalence.logic.hol", name = "Ty")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyTy(Ty);

/// An opaque, portable HOL term handle.
#[pyclass(frozen, module = "covalence.logic.hol", name = "Tm")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyTm(Tm);

/// An owning wrapper over an admitted HOL arena.
///
/// The compiled class has a distinct private name because the extension also
/// contains the LRAT kernel. `covalence.logic.hol` exports it as `Kernel`.
#[pyclass(frozen, module = "covalence.logic.hol", name = "HolKernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel(Kernel);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    /// Construct an empty admitted arena.
    #[staticmethod]
    fn empty() -> Self {
        Self(Kernel::empty())
    }

    /// Return a replacement kernel and a Boolean type handle.
    fn bool_ty(&self, python: Python<'_>) -> PyResult<(Py<Self>, Py<PyTy>)> {
        let (kernel, ty) = self.0.bool_ty().map_err(rejection)?;
        Ok((Py::new(python, Self(kernel))?, Py::new(python, PyTy(ty))?))
    }

    /// Return a replacement kernel and a Boolean constant handle.
    fn bool_const(&self, python: Python<'_>, value: bool) -> PyResult<(Py<Self>, Py<PyTm>)> {
        let (kernel, term) = self.0.bool_const(value).map_err(rejection)?;
        Ok((Py::new(python, Self(kernel))?, Py::new(python, PyTm(term))?))
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyKernel>()?;
    module.add_class::<PyTy>()?;
    module.add_class::<PyTm>()?;
    let error = PyType::new::<HolError>(module.py());
    error.setattr("__module__", "covalence.logic.hol")?;
    module.add("HolError", error)
}
