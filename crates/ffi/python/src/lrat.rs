//! `covalence-logic-lrat` at the Python boundary.

// PyO3 extracts Python sequences into owned vectors before calling these
// methods. The apparent pass-by-value choices are its boundary convention.
#![allow(clippy::needless_pass_by_value)]

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_lrat::{Error, Kernel, RatGroup};
use covalence_logic_sat::cnf::Literal;

use crate::sat::{PyClause, PyFormula, PyLiteral};

create_exception!(
    covalence,
    LratError,
    PyValueError,
    "A typed LRAT operation was rejected."
);

fn rejection(error: Error) -> PyErr {
    LratError::new_err(error.to_string())
}

/// One explicitly delimited RAT resolvent check.
#[pyclass(frozen, module = "covalence.logic.lrat", name = "RatGroup")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRatGroup {
    #[pyo3(get)]
    opposing_clause_id: u64,
    #[pyo3(get)]
    resolvent_rup_hints: Vec<u64>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRatGroup {
    #[new]
    fn new(opposing_clause_id: u64, resolvent_rup_hints: Vec<u64>) -> Self {
        Self {
            opposing_clause_id,
            resolvent_rup_hints,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "RatGroup({}, {:?})",
            self.opposing_clause_id, self.resolvent_rup_hints
        )
    }
}

/// A parser-independent typed LRAT clause kernel.
#[pyclass(module = "covalence.logic.lrat", name = "Kernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel {
    kernel: Kernel,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    /// Opens initial clauses numbered from one.
    #[new]
    fn new(initial: PyRef<'_, PyFormula>) -> Self {
        Self {
            kernel: Kernel::open(&initial.0),
        }
    }

    /// Whether the empty clause has been learned or was initially present.
    #[getter]
    fn refuted(&self) -> bool {
        self.kernel.refuted()
    }

    /// The greatest clause identifier allocated so far.
    #[getter]
    fn high_water(&self) -> u64 {
        self.kernel.high_water()
    }

    /// Returns a copy of a live clause, or `None` for an unknown identifier.
    fn clause(&self, id: u64) -> Option<Vec<i64>> {
        self.kernel
            .clause(id)
            .map(|clause| clause.iter().map(Literal::get).collect())
    }

    /// Learns a clause by ordered reverse unit propagation.
    fn learn_rup(
        &mut self,
        id: u64,
        clause: PyRef<'_, PyClause>,
        ordered_hints: Vec<u64>,
    ) -> PyResult<()> {
        self.kernel
            .learn_rup(id, &clause.0, &ordered_hints)
            .map_err(rejection)
    }

    /// Learns a clause by explicit resolution asymmetric tautology groups.
    fn learn_rat(
        &mut self,
        id: u64,
        clause: PyRef<'_, PyClause>,
        pivot: PyRef<'_, PyLiteral>,
        prefix_rup_hints: Vec<u64>,
        groups: Vec<PyRef<'_, PyRatGroup>>,
    ) -> PyResult<()> {
        let groups = groups
            .iter()
            .map(|group| RatGroup {
                opposing_clause_id: group.opposing_clause_id,
                resolvent_rup_hints: group.resolvent_rup_hints.clone(),
            })
            .collect::<Vec<_>>();
        self.kernel
            .learn_rat(id, &clause.0, pivot.0, &prefix_rup_hints, &groups)
            .map_err(rejection)
    }

    /// Deletes live clauses without lowering the identifier high-water mark.
    fn forget(&mut self, ids: Vec<u64>) -> PyResult<()> {
        self.kernel.forget(&ids).map_err(rejection)
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyKernel>()?;
    module.add_class::<PyRatGroup>()?;

    let error = PyType::new::<LratError>(module.py());
    error.setattr("__module__", "covalence.logic.lrat")?;
    module.add("LratError", error)
}
