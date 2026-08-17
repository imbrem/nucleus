//! `covalence-logic-bdd` at the Python boundary.

#![allow(
    clippy::needless_pass_by_value,
    clippy::unused_self,
    clippy::wrong_self_convention
)]

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard};

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{IntoPyObjectExt, basic::CompareOp, types::PyType};
use covalence_logic_bdd::{
    Bdd, BddError as Error, CnfEncoding, Diagram, DiagramKind, Manager, Variable,
};

use crate::sat::PyFormula;

create_exception!(
    covalence,
    BddError,
    PyValueError,
    "A binary-decision-diagram operation was rejected."
);

fn rejected(error: Error) -> PyErr {
    BddError::new_err(error.to_string())
}

fn variable(value: u64) -> PyResult<Variable> {
    Variable::new(value).map_err(rejected)
}

type SharedManager = Arc<Mutex<Manager>>;

fn lock(manager: &SharedManager) -> PyResult<MutexGuard<'_, Manager>> {
    manager
        .lock()
        .map_err(|_| BddError::new_err("BDD manager lock is poisoned"))
}

/// General, potentially non-canonical decision syntax.
#[pyclass(
    frozen,
    eq,
    skip_from_py_object,
    module = "covalence.logic.bdd",
    name = "Diagram"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Eq, PartialEq)]
pub struct PyDiagram(Diagram);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyDiagram {
    #[staticmethod]
    fn constant(value: bool) -> Self {
        Self(Diagram::constant(value))
    }

    #[staticmethod]
    fn branch(variable_number: u64, low: PyRef<'_, Self>, high: PyRef<'_, Self>) -> PyResult<Self> {
        Ok(Self(Diagram::branch(
            variable(variable_number)?,
            low.0.clone(),
            high.0.clone(),
        )))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.0.kind() {
            DiagramKind::Constant(_) => "constant",
            DiagramKind::Branch { .. } => "branch",
        }
    }

    #[getter]
    fn value(&self) -> Option<bool> {
        match self.0.kind() {
            DiagramKind::Constant(value) => Some(value),
            DiagramKind::Branch { .. } => None,
        }
    }

    #[getter]
    fn variable(&self) -> Option<u64> {
        match self.0.kind() {
            DiagramKind::Constant(_) => None,
            DiagramKind::Branch { variable, .. } => Some(variable.get()),
        }
    }

    #[getter]
    fn low(&self) -> Option<Self> {
        match self.0.kind() {
            DiagramKind::Constant(_) => None,
            DiagramKind::Branch { low, .. } => Some(Self(low.clone())),
        }
    }

    #[getter]
    fn high(&self) -> Option<Self> {
        match self.0.kind() {
            DiagramKind::Constant(_) => None,
            DiagramKind::Branch { high, .. } => Some(Self(high.clone())),
        }
    }

    fn evaluate(&self, assignment: HashMap<u64, bool>) -> PyResult<bool> {
        self.0
            .evaluate(|variable| assignment.get(&variable.get()).copied())
            .map_err(rejected)
    }

    fn __repr__(&self) -> String {
        match self.0.kind() {
            DiagramKind::Constant(value) => format!("Diagram.constant({value})"),
            DiagramKind::Branch { variable, .. } => {
                format!("Diagram.branch({}, ...)", variable.get())
            }
        }
    }
}

/// A canonical reduced ordered BDD manager.
#[pyclass(frozen, module = "covalence.logic.bdd", name = "BddManager")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyBddManager {
    manager: SharedManager,
}

impl PyBddManager {
    fn wrap(&self, root: Bdd) -> PyBdd {
        PyBdd {
            manager: Arc::clone(&self.manager),
            root,
        }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyBddManager {
    #[new]
    fn new() -> Self {
        Self {
            manager: Arc::new(Mutex::new(Manager::new())),
        }
    }

    fn constant(&self, value: bool) -> PyResult<PyBdd> {
        let root = lock(&self.manager)?.constant(value);
        Ok(self.wrap(root))
    }

    fn variable(&self, variable_number: u64) -> PyResult<PyBdd> {
        let root = lock(&self.manager)?.variable(variable(variable_number)?);
        Ok(self.wrap(root))
    }

    fn reduce(&self, diagram: PyRef<'_, PyDiagram>) -> PyResult<PyBdd> {
        let root = lock(&self.manager)?.reduce(&diagram.0);
        Ok(self.wrap(root))
    }

    fn from_cnf(&self, formula: PyRef<'_, PyFormula>) -> PyResult<PyBdd> {
        let root = lock(&self.manager)?
            .from_cnf(&formula.0)
            .map_err(rejected)?;
        Ok(self.wrap(root))
    }
}

/// A canonical BDD tied to one manager.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.bdd",
    name = "Bdd"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyBdd {
    manager: SharedManager,
    root: Bdd,
}

impl PyBdd {
    fn wrap(&self, root: Bdd) -> Self {
        Self {
            manager: Arc::clone(&self.manager),
            root,
        }
    }

    fn binary(
        &self,
        other: &Self,
        operation: impl FnOnce(&mut Manager, Bdd, Bdd) -> Result<Bdd, Error>,
    ) -> PyResult<Self> {
        let mut manager = lock(&self.manager)?;
        let root = operation(&mut manager, self.root, other.root).map_err(rejected)?;
        Ok(self.wrap(root))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyBdd {
    fn __and__(&self, other: PyRef<'_, Self>) -> PyResult<Self> {
        self.binary(&other, Manager::and)
    }

    fn __or__(&self, other: PyRef<'_, Self>) -> PyResult<Self> {
        self.binary(&other, Manager::or)
    }

    fn __xor__(&self, other: PyRef<'_, Self>) -> PyResult<Self> {
        self.binary(&other, Manager::xor)
    }

    fn __invert__(&self) -> PyResult<Self> {
        let root = lock(&self.manager)?.not(self.root).map_err(rejected)?;
        Ok(self.wrap(root))
    }

    fn implies(&self, conclusion: PyRef<'_, Self>) -> PyResult<Self> {
        self.binary(&conclusion, Manager::implication)
    }

    fn equivalent(&self, other: PyRef<'_, Self>) -> PyResult<Self> {
        self.binary(&other, Manager::equivalence)
    }

    fn if_then_else(
        &self,
        then_value: PyRef<'_, Self>,
        else_value: PyRef<'_, Self>,
    ) -> PyResult<Self> {
        let root = lock(&self.manager)?
            .if_then_else(self.root, then_value.root, else_value.root)
            .map_err(rejected)?;
        Ok(self.wrap(root))
    }

    fn exists(&self, variable_number: u64) -> PyResult<Self> {
        let root = lock(&self.manager)?
            .exists(variable(variable_number)?, self.root)
            .map_err(rejected)?;
        Ok(self.wrap(root))
    }

    fn evaluate(&self, assignment: HashMap<u64, bool>) -> PyResult<bool> {
        lock(&self.manager)?
            .evaluate(self.root, |variable| {
                assignment.get(&variable.get()).copied()
            })
            .map_err(rejected)
    }

    fn to_diagram(&self) -> PyResult<PyDiagram> {
        lock(&self.manager)?
            .to_diagram(self.root)
            .map(PyDiagram)
            .map_err(rejected)
    }

    fn to_cnf(&self) -> PyResult<PyCnfEncoding> {
        lock(&self.manager)?
            .to_cnf(self.root)
            .map(PyCnfEncoding)
            .map_err(rejected)
    }

    #[getter]
    fn variables(&self) -> PyResult<Vec<u64>> {
        lock(&self.manager)?
            .variables(self.root)
            .map(|variables| variables.into_iter().map(Variable::get).collect())
            .map_err(rejected)
    }

    #[getter]
    fn node_count(&self) -> PyResult<usize> {
        lock(&self.manager)?.node_count(self.root).map_err(rejected)
    }

    #[getter]
    fn is_true(&self) -> PyResult<bool> {
        Ok(lock(&self.manager)?.is_true(self.root))
    }

    #[getter]
    fn is_false(&self) -> PyResult<bool> {
        Ok(lock(&self.manager)?.is_false(self.root))
    }

    fn __bool__(&self) -> PyResult<bool> {
        Err(PyTypeError::new_err(
            "BDD truth is symbolic; use is_true, is_false, or evaluate()",
        ))
    }

    fn __richcmp__(
        &self,
        other: &Bound<'_, PyAny>,
        operation: CompareOp,
        python: Python<'_>,
    ) -> PyResult<Py<PyAny>> {
        let Ok(other) = other.cast::<Self>() else {
            return Ok(python.NotImplemented());
        };
        match operation {
            CompareOp::Eq => (self.root == other.get().root).into_py_any(python),
            CompareOp::Ne => (self.root != other.get().root).into_py_any(python),
            _ => Ok(python.NotImplemented()),
        }
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!(
            "Bdd(variables={:?}, node_count={})",
            self.variables()?,
            self.node_count()?
        ))
    }
}

/// A Tseitin CNF plus its fresh auxiliary variables.
#[pyclass(frozen, module = "covalence.logic.bdd", name = "CnfEncoding")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCnfEncoding(CnfEncoding);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCnfEncoding {
    #[getter]
    fn formula(&self) -> PyFormula {
        PyFormula(self.0.formula().clone())
    }

    #[getter]
    fn introduced_variables(&self) -> Vec<u64> {
        self.0
            .introduced_variables()
            .iter()
            .copied()
            .map(Variable::get)
            .collect()
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyDiagram>()?;
    module.add_class::<PyBddManager>()?;
    module.add_class::<PyBdd>()?;
    module.add_class::<PyCnfEncoding>()?;
    PyType::new::<PyBdd>(module.py()).setattr("__hash__", module.py().None())?;
    let error = PyType::new::<BddError>(module.py());
    error.setattr("__module__", "covalence.logic.bdd")?;
    module.add("BddError", error)
}
