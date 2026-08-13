//! `covalence-logic-lrat` at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_lrat::{
    Error, Kernel, RatGroup,
    parse::{Step, parse_binary, parse_text},
};
use covalence_logic_sat::cnf::Literal;

use crate::sat::{PyClause, PyFormula, PyLiteral};

create_exception!(
    covalence,
    LratError,
    PyValueError,
    "A typed LRAT operation was rejected."
);

fn rejection(error: impl std::fmt::Display) -> PyErr {
    LratError::new_err(error.to_string())
}

#[pyclass(frozen, module = "covalence.logic.lrat", name = "RatGroup")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRatGroup {
    #[pyo3(get)]
    opposing_clause_id: u64,
    #[pyo3(get)]
    resolvent_rup_hints: Vec<u64>,
}

impl PyRatGroup {
    fn value(&self) -> RatGroup {
        RatGroup {
            opposing_clause_id: self.opposing_clause_id,
            resolvent_rup_hints: self.resolvent_rup_hints.clone(),
        }
    }
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

/// One typed LRAT proof step.
#[pyclass(frozen, module = "covalence.logic.lrat", name = "Step")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyStep(Step);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyStep {
    #[staticmethod]
    fn rup(id: u64, clause: PyRef<'_, PyClause>, ordered_hints: Vec<u64>) -> Self {
        Self(Step::LearnRup {
            id,
            clause: clause.0.clone(),
            ordered_hints,
        })
    }

    #[staticmethod]
    fn rat(
        id: u64,
        clause: PyRef<'_, PyClause>,
        pivot: PyRef<'_, PyLiteral>,
        prefix_rup_hints: Vec<u64>,
        groups: Vec<PyRef<'_, PyRatGroup>>,
    ) -> Self {
        Self(Step::LearnRat {
            id,
            clause: clause.0.clone(),
            pivot: pivot.0,
            prefix_rup_hints,
            groups: groups.iter().map(|group| group.value()).collect(),
        })
    }

    #[staticmethod]
    fn forget(ids: Vec<u64>) -> Self {
        Self(Step::Forget { ids })
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.0 {
            Step::LearnRup { .. } => "rup",
            Step::LearnRat { .. } => "rat",
            Step::Forget { .. } => "forget",
        }
    }

    #[getter]
    fn id(&self) -> Option<u64> {
        match self.0 {
            Step::LearnRup { id, .. } | Step::LearnRat { id, .. } => Some(id),
            Step::Forget { .. } => None,
        }
    }

    #[getter]
    fn clause(&self, python: Python<'_>) -> PyResult<Option<Py<PyClause>>> {
        match &self.0 {
            Step::LearnRup { clause, .. } | Step::LearnRat { clause, .. } => {
                Ok(Some(Py::new(python, PyClause(clause.clone()))?))
            }
            Step::Forget { .. } => Ok(None),
        }
    }

    #[getter]
    fn ids(&self) -> Option<Vec<u64>> {
        match &self.0 {
            Step::Forget { ids } => Some(ids.clone()),
            _ => None,
        }
    }

    #[getter]
    fn ordered_hints(&self) -> Option<Vec<u64>> {
        match &self.0 {
            Step::LearnRup { ordered_hints, .. } => Some(ordered_hints.clone()),
            _ => None,
        }
    }
}

fn wrap_steps(python: Python<'_>, steps: Vec<Step>) -> PyResult<Vec<Py<PyStep>>> {
    steps
        .into_iter()
        .map(|step| Py::new(python, PyStep(step)))
        .collect()
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "parse_text")]
fn parse_text_python(python: Python<'_>, text: &str) -> PyResult<Vec<Py<PyStep>>> {
    wrap_steps(python, parse_text(text).map_err(rejection)?)
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "parse_binary")]
fn parse_binary_python(python: Python<'_>, proof: Bytes) -> PyResult<Vec<Py<PyStep>>> {
    wrap_steps(python, parse_binary(proof.as_slice()).map_err(rejection)?)
}

#[pyclass(module = "covalence.logic.lrat", name = "Kernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel {
    kernel: Kernel,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    #[new]
    fn new(initial: PyRef<'_, PyFormula>) -> Self {
        Self {
            kernel: Kernel::open(&initial.0),
        }
    }

    #[getter]
    fn refuted(&self) -> bool {
        self.kernel.refuted()
    }

    #[getter]
    fn high_water(&self) -> u64 {
        self.kernel.high_water()
    }

    fn clause(&self, id: u64) -> Option<Vec<i64>> {
        self.kernel
            .clause(id)
            .map(|clause| clause.iter().map(Literal::get).collect())
    }

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

    fn learn_rat(
        &mut self,
        id: u64,
        clause: PyRef<'_, PyClause>,
        pivot: PyRef<'_, PyLiteral>,
        prefix_rup_hints: Vec<u64>,
        groups: Vec<PyRef<'_, PyRatGroup>>,
    ) -> PyResult<()> {
        let groups = groups.iter().map(|group| group.value()).collect::<Vec<_>>();
        self.kernel
            .learn_rat(id, &clause.0, pivot.0, &prefix_rup_hints, &groups)
            .map_err(rejection)
    }

    fn forget(&mut self, ids: Vec<u64>) -> PyResult<()> {
        self.kernel.forget(&ids).map_err(rejection)
    }

    fn verify(&mut self, proof: &Bound<'_, PyAny>) -> PyResult<()> {
        let mut candidate = self.kernel.clone();
        if candidate.refuted() {
            return Ok(());
        }
        if let Ok(text) = proof.extract::<String>() {
            for step in parse_text(&text).map_err(rejection)? {
                step.apply(&mut candidate).map_err(rejection)?;
                if candidate.refuted() {
                    break;
                }
            }
        } else if let Ok(bytes) = proof.extract::<Bytes>() {
            for step in parse_binary(bytes.as_slice()).map_err(rejection)? {
                step.apply(&mut candidate).map_err(rejection)?;
                if candidate.refuted() {
                    break;
                }
            }
        } else {
            for item in proof.try_iter()? {
                item?
                    .extract::<PyRef<'_, PyStep>>()?
                    .0
                    .apply(&mut candidate)
                    .map_err(rejection)?;
                if candidate.refuted() {
                    break;
                }
            }
        }
        if !candidate.refuted() {
            return Err(rejection(Error::NoRefutation));
        }
        self.kernel = candidate;
        Ok(())
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyKernel>()?;
    module.add_class::<PyRatGroup>()?;
    module.add_class::<PyStep>()?;
    for function in [
        wrap_pyfunction!(parse_text_python, module)?,
        wrap_pyfunction!(parse_binary_python, module)?,
    ] {
        function.setattr("__module__", "covalence.logic.lrat")?;
        module.add_function(function)?;
    }
    let error = PyType::new::<LratError>(module.py());
    error.setattr("__module__", "covalence.logic.lrat")?;
    module.add("LratError", error)
}
