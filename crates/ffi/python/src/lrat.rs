//! `covalence-logic-lrat` at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use std::fmt::Write as _;

use crate::sat::{PyClause, PyLiteral};
use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_hol::{ClassicalKernel, Cnf, Dnf, Lit, LitVec, Refutation, ThmId};
use covalence_logic_lrat::{
    Formula, RatGroup,
    parse::{
        Step, encode_binary_dimacs, parse_binary, parse_binary_dimacs, parse_dimacs, parse_text,
    },
    replay,
};

create_exception!(
    covalence,
    LratError,
    PyValueError,
    "A typed LRAT operation was rejected."
);

fn rejection(error: impl std::fmt::Display) -> PyErr {
    LratError::new_err(error.to_string())
}

fn rows(rows: Vec<Vec<i32>>) -> PyResult<Vec<LitVec>> {
    rows.into_iter()
        .map(|row| {
            row.into_iter()
                .map(|literal| Lit::try_new(literal).map_err(rejection))
                .collect()
        })
        .collect()
}

fn formula(cnf: &Cnf) -> PyResult<Formula> {
    Formula::from_signed(
        cnf.rows()
            .map(|row| row.iter().map(|literal| i64::from(literal.get()))),
    )
    .map_err(rejection)
}

type PyClassicalSequent = (Vec<Vec<i32>>, Vec<Vec<i32>>);

#[pyclass(module = "covalence.logic.classical", name = "Cnf")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCnf(pub(crate) Cnf);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCnf {
    #[new]
    fn new(value: Vec<Vec<i32>>) -> PyResult<Self> {
        Ok(Self(Cnf::new(rows(value)?)))
    }

    #[staticmethod]
    fn from_dimacs(dimacs: Bytes) -> PyResult<Self> {
        covalence_logic_lrat::load_cnf(&parse_dimacs(dimacs.as_slice()).map_err(rejection)?)
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn from_binary_dimacs(dimacs: Bytes) -> PyResult<Self> {
        covalence_logic_lrat::load_cnf(&parse_binary_dimacs(dimacs.as_slice()).map_err(rejection)?)
            .map(Self)
            .map_err(rejection)
    }

    #[getter]
    fn rows(&self) -> Vec<Vec<i32>> {
        self.0
            .rows()
            .map(|row| row.iter().map(|literal| literal.get()).collect())
            .collect()
    }

    fn normalize(&mut self) {
        self.0.normalize();
    }

    fn to_dimacs(&self) -> Vec<u8> {
        let mut text = format!(
            "p cnf {} {}\n",
            formula(&self.0)
                .expect("i32 literals are DIMACS literals")
                .max_variable(),
            self.0.rows().count()
        );
        for row in self.0.rows() {
            for literal in row {
                write!(text, "{} ", literal.get()).expect("writing to a string is infallible");
            }
            text.push_str("0\n");
        }
        text.into_bytes()
    }

    fn to_binary_dimacs(&self) -> PyResult<Vec<u8>> {
        Ok(encode_binary_dimacs(&formula(&self.0)?))
    }
}

#[pyclass(module = "covalence.logic.classical", name = "Dnf")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyDnf(Dnf);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyDnf {
    #[new]
    fn new(value: Vec<Vec<i32>>) -> PyResult<Self> {
        Ok(Self(Dnf::new(rows(value)?)))
    }

    #[getter]
    fn rows(&self) -> Vec<Vec<i32>> {
        self.0
            .rows()
            .map(|row| row.iter().map(|literal| literal.get()).collect())
            .collect()
    }

    fn normalize(&mut self) {
        self.0.normalize();
    }
}

#[pyclass(frozen, module = "covalence.logic.classical", name = "Refutation")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRefutation(pub(crate) Refutation);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRefutation {
    #[staticmethod]
    fn from_text_lrat(cnf: PyRef<'_, PyCnf>, proof: &str) -> PyResult<Self> {
        replay(&formula(&cnf.0)?, &parse_text(proof).map_err(rejection)?)
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn from_binary_lrat(cnf: PyRef<'_, PyCnf>, proof: Bytes) -> PyResult<Self> {
        replay(
            &formula(&cnf.0)?,
            &parse_binary(proof.as_slice()).map_err(rejection)?,
        )
        .map(Self)
        .map_err(rejection)
    }

    #[getter]
    fn cnf(&self) -> PyCnf {
        PyCnf(self.0.theorem().lhs.to_owned())
    }
}

#[pyclass(module = "covalence.logic.classical", name = "ClassicalKernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyClassicalKernel(ClassicalKernel);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyClassicalKernel {
    #[new]
    fn new() -> Self {
        Self(ClassicalKernel::new())
    }

    fn copy_refutation(&mut self, refutation: PyRef<'_, PyRefutation>) -> PyResult<i32> {
        self.0
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(rejection)
    }

    fn theorem(&self, theorem: i32) -> PyResult<PyClassicalSequent> {
        let id =
            ThmId::new(theorem).ok_or_else(|| rejection("theorem IDs are positive i32 values"))?;
        let theorem = self
            .0
            .get(id)
            .ok_or_else(|| rejection("theorem is absent"))?;
        Ok((
            theorem
                .lhs
                .rows()
                .map(|row| row.iter().map(|literal| literal.get()).collect())
                .collect(),
            theorem
                .rhs
                .rows()
                .map(|row| row.iter().map(|literal| literal.get()).collect())
                .collect(),
        ))
    }
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

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCnf>()?;
    module.add_class::<PyDnf>()?;
    module.add_class::<PyRefutation>()?;
    module.add_class::<PyClassicalKernel>()?;
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
