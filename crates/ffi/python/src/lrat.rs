//! `covalence-logic-lrat` at the Python boundary.

// PyO3 extracts Python sequences into owned vectors before calling these
// methods. The apparent pass-by-value choices are its boundary convention.
#![allow(clippy::needless_pass_by_value)]

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{exceptions::PyRuntimeError, types::PyType};
use covalence_logic_lrat::{Call, Error, Kernel, RatGroup, parse_binary, parse_text};
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

fn rat_group(group: &PyRatGroup) -> RatGroup {
    RatGroup {
        opposing_clause_id: group.opposing_clause_id,
        resolvent_rup_hints: group.resolvent_rup_hints.clone(),
    }
}

#[pyclass(frozen, module = "covalence.logic.lrat", name = "RupStep")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRupStep {
    id: u64,
    clause: covalence_logic_sat::cnf::Clause,
    ordered_hints: Vec<u64>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRupStep {
    #[new]
    fn new(id: u64, clause: PyRef<'_, PyClause>, ordered_hints: Vec<u64>) -> Self {
        Self {
            id,
            clause: clause.0.clone(),
            ordered_hints,
        }
    }

    #[getter]
    fn id(&self) -> u64 {
        self.id
    }

    #[getter]
    fn clause(&self, python: Python<'_>) -> PyResult<Py<PyClause>> {
        Py::new(python, PyClause(self.clause.clone()))
    }

    #[getter]
    fn ordered_hints(&self) -> Vec<u64> {
        self.ordered_hints.clone()
    }
}

#[pyclass(frozen, module = "covalence.logic.lrat", name = "RatStep")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRatStep {
    id: u64,
    clause: covalence_logic_sat::cnf::Clause,
    pivot: Literal,
    prefix_rup_hints: Vec<u64>,
    groups: Vec<RatGroup>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRatStep {
    #[new]
    fn new(
        id: u64,
        clause: PyRef<'_, PyClause>,
        pivot: PyRef<'_, PyLiteral>,
        prefix_rup_hints: Vec<u64>,
        groups: Vec<PyRef<'_, PyRatGroup>>,
    ) -> Self {
        Self {
            id,
            clause: clause.0.clone(),
            pivot: pivot.0,
            prefix_rup_hints,
            groups: groups.iter().map(|group| rat_group(group)).collect(),
        }
    }

    #[getter]
    fn id(&self) -> u64 {
        self.id
    }

    #[getter]
    fn clause(&self, python: Python<'_>) -> PyResult<Py<PyClause>> {
        Py::new(python, PyClause(self.clause.clone()))
    }

    #[getter]
    fn pivot(&self, python: Python<'_>) -> PyResult<Py<PyLiteral>> {
        Py::new(python, PyLiteral(self.pivot))
    }

    #[getter]
    fn prefix_rup_hints(&self) -> Vec<u64> {
        self.prefix_rup_hints.clone()
    }

    #[getter]
    fn groups(&self, python: Python<'_>) -> PyResult<Vec<Py<PyRatGroup>>> {
        self.groups
            .iter()
            .map(|group| {
                Py::new(
                    python,
                    PyRatGroup {
                        opposing_clause_id: group.opposing_clause_id,
                        resolvent_rup_hints: group.resolvent_rup_hints.clone(),
                    },
                )
            })
            .collect()
    }
}

#[pyclass(frozen, module = "covalence.logic.lrat", name = "ForgetStep")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyForgetStep {
    ids: Vec<u64>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyForgetStep {
    #[new]
    fn new(ids: Vec<u64>) -> Self {
        Self { ids }
    }

    #[getter]
    fn ids(&self) -> Vec<u64> {
        self.ids.clone()
    }
}

fn call_from_python(value: &Bound<'_, PyAny>) -> PyResult<Call> {
    if let Ok(step) = value.extract::<PyRef<'_, PyRupStep>>() {
        return Ok(Call::LearnRup {
            id: step.id,
            clause: step.clause.clone(),
            ordered_hints: step.ordered_hints.clone(),
        });
    }
    if let Ok(step) = value.extract::<PyRef<'_, PyRatStep>>() {
        return Ok(Call::LearnRat {
            id: step.id,
            clause: step.clause.clone(),
            pivot: step.pivot,
            prefix_rup_hints: step.prefix_rup_hints.clone(),
            groups: step.groups.clone(),
        });
    }
    if let Ok(step) = value.extract::<PyRef<'_, PyForgetStep>>() {
        return Ok(Call::Forget {
            ids: step.ids.clone(),
        });
    }
    Err(PyTypeError::new_err(
        "LRAT steps must be RupStep, RatStep, or ForgetStep",
    ))
}

fn wrap_call(python: Python<'_>, call: Call) -> PyResult<Py<PyAny>> {
    match call {
        Call::LearnRup {
            id,
            clause,
            ordered_hints,
        } => Ok(Py::new(
            python,
            PyRupStep {
                id,
                clause,
                ordered_hints,
            },
        )?
        .into_any()),
        Call::LearnRat {
            id,
            clause,
            pivot,
            prefix_rup_hints,
            groups,
        } => Ok(Py::new(
            python,
            PyRatStep {
                id,
                clause,
                pivot,
                prefix_rup_hints,
                groups,
            },
        )?
        .into_any()),
        Call::Forget { ids } => Ok(Py::new(python, PyForgetStep { ids })?.into_any()),
        _ => Err(PyRuntimeError::new_err("unsupported LRAT call variant")),
    }
}

fn wrap_calls(python: Python<'_>, calls: Vec<Call>) -> PyResult<Vec<Py<PyAny>>> {
    calls
        .into_iter()
        .map(|call| wrap_call(python, call))
        .collect()
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "parse_text")]
fn parse_text_python(python: Python<'_>, text: &str) -> PyResult<Vec<Py<PyAny>>> {
    wrap_calls(
        python,
        parse_text(text).map_err(|error| LratError::new_err(error.to_string()))?,
    )
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "parse_binary")]
fn parse_binary_python(python: Python<'_>, proof: Bytes) -> PyResult<Vec<Py<PyAny>>> {
    wrap_calls(
        python,
        parse_binary(proof.as_slice()).map_err(|error| LratError::new_err(error.to_string()))?,
    )
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

    /// Checks a complete text, binary, or typed LRAT proof transactionally.
    fn verify(&mut self, proof: &Bound<'_, PyAny>) -> PyResult<()> {
        let mut candidate = self.kernel.clone();
        if candidate.refuted() {
            return Ok(());
        }
        if let Ok(text) = proof.extract::<String>() {
            let calls = parse_text(&text).map_err(|error| LratError::new_err(error.to_string()))?;
            for call in &calls {
                candidate.apply(call).map_err(rejection)?;
                if candidate.refuted() {
                    break;
                }
            }
        } else if let Ok(bytes) = proof.extract::<Bytes>() {
            let calls = parse_binary(bytes.as_slice())
                .map_err(|error| LratError::new_err(error.to_string()))?;
            for call in &calls {
                candidate.apply(call).map_err(rejection)?;
                if candidate.refuted() {
                    break;
                }
            }
        } else {
            for item in proof.try_iter()? {
                candidate
                    .apply(&call_from_python(&item?)?)
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
    module.add_class::<PyRupStep>()?;
    module.add_class::<PyRatStep>()?;
    module.add_class::<PyForgetStep>()?;
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
