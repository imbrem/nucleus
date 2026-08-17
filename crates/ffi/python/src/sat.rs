//! `covalence-logic-sat` at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_sat::cnf::{Clause, Error, Formula, Literal};

create_exception!(
    covalence,
    CnfError,
    PyValueError,
    "A conjunctive-normal-form value was malformed."
);

fn malformed(error: Error) -> PyErr {
    CnfError::new_err(error.to_string())
}

#[pyclass(
    frozen,
    eq,
    ord,
    hash,
    module = "covalence.logic.sat",
    name = "Literal"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PyLiteral(pub(crate) Literal);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyLiteral {
    #[new]
    fn new(value: i64) -> PyResult<Self> {
        Ok(Self(Literal::new(value).map_err(malformed)?))
    }

    #[getter]
    fn value(&self) -> i64 {
        self.0.get()
    }

    #[getter]
    fn variable(&self) -> u64 {
        self.0.variable()
    }

    fn __int__(&self) -> i64 {
        self.0.get()
    }

    fn __neg__(&self) -> Self {
        Self(-self.0)
    }

    fn __repr__(&self) -> String {
        format!("Literal({})", self.0.get())
    }
}

#[pyclass(frozen, eq, ord, hash, module = "covalence.logic.sat", name = "Clause")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PyClause(pub(crate) Clause);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyClause {
    #[new]
    fn new(literals: Vec<i64>) -> PyResult<Self> {
        Ok(Self(Clause::from_signed(literals).map_err(malformed)?))
    }

    #[getter]
    fn literals(&self) -> Vec<i64> {
        self.0.iter().map(Literal::get).collect()
    }

    fn __len__(&self) -> usize {
        self.0.literals().len()
    }

    fn __repr__(&self) -> String {
        format!("Clause({:?})", self.literals())
    }
}

#[pyclass(
    frozen,
    eq,
    ord,
    hash,
    module = "covalence.logic.sat",
    name = "Formula"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PyFormula(pub(crate) Formula);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyFormula {
    #[new]
    fn new(clauses: Vec<PyRef<'_, PyClause>>) -> Self {
        Self(Formula::new(clauses.iter().map(|clause| clause.0.clone())))
    }

    #[getter]
    fn clauses(&self, python: Python<'_>) -> PyResult<Vec<Py<PyClause>>> {
        self.0
            .clauses()
            .iter()
            .cloned()
            .map(|clause| Py::new(python, PyClause(clause)))
            .collect()
    }

    #[getter]
    fn max_variable(&self) -> u64 {
        self.0.max_variable()
    }

    fn __len__(&self) -> usize {
        self.0.len()
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyLiteral>()?;
    module.add_class::<PyClause>()?;
    module.add_class::<PyFormula>()?;
    let error = PyType::new::<CnfError>(module.py());
    error.setattr("__module__", "covalence.logic.sat")?;
    module.add("CnfError", error)
}
