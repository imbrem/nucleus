//! `covalence-logic-metamath` at the Python boundary.

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_logic_metamath::{
    Assertion, Database, Expr, FileResolver, Statement, SymbolKind, parse, parse_with_resolver,
    verify_all,
};

create_exception!(
    covalence,
    MetamathError,
    PyValueError,
    "A Metamath database could not be parsed or validated."
);

fn rejection(error: impl std::fmt::Display) -> PyErr {
    MetamathError::new_err(error.to_string())
}

#[pyclass(frozen, module = "covalence.logic.metamath", name = "Expression")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyExpression {
    #[pyo3(get)]
    typecode: String,
    #[pyo3(get)]
    body: Vec<String>,
}

impl From<&Expr> for PyExpression {
    fn from(expression: &Expr) -> Self {
        Self {
            typecode: expression.typecode().to_owned(),
            body: expression.body().iter().map(ToString::to_string).collect(),
        }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyExpression {
    fn __str__(&self) -> String {
        std::iter::once(self.typecode.as_str())
            .chain(self.body.iter().map(String::as_str))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn __repr__(&self) -> String {
        format!("Expression({:?}, {:?})", self.typecode, self.body)
    }
}

#[pyclass(frozen, module = "covalence.logic.metamath", name = "Assertion")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyAssertion {
    #[pyo3(get)]
    label: String,
    #[pyo3(get)]
    conclusion: Py<PyExpression>,
    #[pyo3(get)]
    hypothesis_labels: Vec<String>,
    #[pyo3(get)]
    disjoint_pairs: Vec<(String, String)>,
    #[pyo3(get)]
    proof_encoding: Option<&'static str>,
}

impl PyAssertion {
    fn new(python: Python<'_>, assertion: &Assertion) -> PyResult<Self> {
        let mut hypothesis_labels = assertion
            .frame
            .floats
            .iter()
            .map(|hypothesis| hypothesis.label.clone())
            .collect::<Vec<_>>();
        hypothesis_labels.extend(
            assertion
                .frame
                .essentials
                .iter()
                .map(|hypothesis| hypothesis.label.clone()),
        );
        let proof_encoding = assertion.proof.as_ref().map(|proof| match proof {
            covalence_logic_metamath::Proof::Normal(_) => "normal",
            covalence_logic_metamath::Proof::Compressed { .. } => "compressed",
        });
        Ok(Self {
            label: assertion.label.clone(),
            conclusion: Py::new(python, PyExpression::from(&assertion.conclusion))?,
            hypothesis_labels,
            disjoint_pairs: assertion.frame.disjoints.clone(),
            proof_encoding,
        })
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyAssertion {
    #[getter]
    fn is_theorem(&self) -> bool {
        self.proof_encoding.is_some()
    }

    fn __repr__(&self) -> String {
        format!("Assertion({:?})", self.label)
    }
}

#[pyclass(module = "covalence.logic.metamath", name = "Database")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyDatabase(Database);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyDatabase {
    #[staticmethod]
    fn parse(source: &str) -> PyResult<Self> {
        parse(source).map(Self).map_err(rejection)
    }

    #[staticmethod]
    fn load(path: &str) -> PyResult<Self> {
        let path = std::path::Path::new(path);
        let filename = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| MetamathError::new_err("path has no UTF-8 filename"))?;
        let resolver =
            FileResolver::new(path.parent().unwrap_or_else(|| std::path::Path::new(".")));
        parse_with_resolver(filename, &resolver)
            .map(Self)
            .map_err(rejection)
    }

    fn validate(&self) -> PyResult<usize> {
        verify_all(&self.0).map_err(rejection)
    }

    #[getter]
    fn statement_count(&self) -> usize {
        self.0.statements().len()
    }

    #[getter]
    fn assertion_count(&self) -> usize {
        self.0.assertions().count()
    }

    #[getter]
    fn theorem_count(&self) -> usize {
        self.0
            .assertions()
            .filter(|assertion| assertion.proof.is_some())
            .count()
    }

    fn symbols(&self, kind: Option<&str>) -> PyResult<Vec<String>> {
        let wanted = match kind {
            None => None,
            Some("constant") => Some(SymbolKind::Constant),
            Some("variable") => Some(SymbolKind::Variable),
            Some(other) => {
                return Err(PyValueError::new_err(format!(
                    "unknown symbol kind {other:?}; expected 'constant' or 'variable'"
                )));
            }
        };
        let mut symbols = self
            .0
            .symbols()
            .filter(|(_, symbol_kind)| wanted.is_none_or(|wanted| wanted == *symbol_kind))
            .map(|(name, _)| name.to_owned())
            .collect::<Vec<_>>();
        symbols.sort_unstable();
        Ok(symbols)
    }

    fn labels(&self) -> Vec<String> {
        self.0
            .statements()
            .iter()
            .filter_map(|statement| match statement {
                Statement::Float(hypothesis) => Some(hypothesis.label.clone()),
                Statement::Essential(hypothesis) => Some(hypothesis.label.clone()),
                Statement::Assert(assertion) => Some(assertion.label.clone()),
                _ => None,
            })
            .collect()
    }

    fn assertion(&self, python: Python<'_>, label: &str) -> PyResult<Option<Py<PyAssertion>>> {
        let Some(Statement::Assert(assertion)) = self.0.statement_by_label(label) else {
            return Ok(None);
        };
        Ok(Some(Py::new(python, PyAssertion::new(python, assertion)?)?))
    }

    fn assertions(&self, python: Python<'_>) -> PyResult<Vec<Py<PyAssertion>>> {
        self.0
            .assertions()
            .map(|assertion| Py::new(python, PyAssertion::new(python, assertion)?))
            .collect()
    }

    fn __len__(&self) -> usize {
        self.0.statements().len()
    }

    fn __repr__(&self) -> String {
        format!(
            "Database(statements={}, assertions={}, theorems={})",
            self.statement_count(),
            self.assertion_count(),
            self.theorem_count()
        )
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add("MetamathError", module.py().get_type::<MetamathError>())?;
    module.add_class::<PyExpression>()?;
    module.add_class::<PyAssertion>()?;
    module.add_class::<PyDatabase>()
}
