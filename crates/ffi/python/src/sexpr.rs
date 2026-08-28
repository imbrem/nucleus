//! `covalence-data-sexpr` at the Python boundary.

// PyO3 extracts owned Rust values for these Python arguments even though this
// thin boundary only reads them.
#![allow(clippy::needless_pass_by_value)]

use covalence_data_sexpr::{
    Atom, Document, ErasedRepr, Event, Expr, ExprKind, Repr, SDocument, SExpr, SExprNode,
    SpannedRepr, parse, parse_one,
};
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::{PyBytes, PyString, PyTuple};

fn value_error(error: impl ToString) -> PyErr {
    PyValueError::new_err(error.to_string())
}

/// An immutable atomic S-expression value.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "Atom"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PySExprAtom {
    atom: Atom,
}

impl PySExprAtom {
    fn wrap(atom: Atom) -> Self {
        Self { atom }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySExprAtom {
    #[staticmethod]
    fn symbol(value: &str) -> Self {
        Self::wrap(Atom::Symbol(value.into()))
    }

    #[staticmethod]
    fn string(value: &str) -> Self {
        Self::wrap(Atom::String(value.into()))
    }

    #[staticmethod]
    fn bytes(value: Bytes) -> Self {
        Self::wrap(Atom::Bytes(value.as_slice().to_vec().into()))
    }

    #[staticmethod]
    fn number(value: &str) -> PyResult<Self> {
        if !value.as_bytes().first().is_some_and(u8::is_ascii_digit) {
            return Err(PyValueError::new_err(
                "number spelling must begin with an ASCII digit",
            ));
        }
        Ok(Self::wrap(Atom::Number(value.into())))
    }

    #[staticmethod]
    fn keyword(value: &str) -> PyResult<Self> {
        if value.is_empty() {
            return Err(PyValueError::new_err("keyword name cannot be empty"));
        }
        Ok(Self::wrap(Atom::Keyword(value.into())))
    }

    #[staticmethod]
    fn directive(value: &str) -> PyResult<Self> {
        if value.is_empty() {
            return Err(PyValueError::new_err("directive name cannot be empty"));
        }
        Ok(Self::wrap(Atom::Directive(value.into())))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.atom {
            Atom::Symbol(_) => "symbol",
            Atom::String(_) => "string",
            Atom::Bytes(_) => "bytes",
            Atom::Number(_) => "number",
            Atom::Keyword(_) => "keyword",
            Atom::Directive(_) => "directive",
        }
    }

    #[getter]
    fn value(&self, python: Python<'_>) -> Py<PyAny> {
        match &self.atom {
            Atom::Bytes(value) => PyBytes::new(python, value).into_any().unbind(),
            Atom::Symbol(value)
            | Atom::String(value)
            | Atom::Number(value)
            | Atom::Keyword(value)
            | Atom::Directive(value) => PyString::new(python, value).into_any().unbind(),
        }
    }

    fn __repr__(&self) -> String {
        format!("Atom(kind='{}')", self.kind())
    }
}

/// One immutable structural S-expression event.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "Event"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PySExprEvent {
    event: Event,
}

impl PySExprEvent {
    fn wrap(event: Event) -> Self {
        Self { event }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySExprEvent {
    #[staticmethod]
    fn open(start: u64, end: u64) -> Self {
        Self::wrap(Event::Open { span: start..end })
    }

    #[staticmethod]
    fn atom(atom: PyRef<'_, PySExprAtom>, start: u64, end: u64) -> Self {
        Self::wrap(Event::Atom {
            value: atom.atom.clone(),
            span: start..end,
        })
    }

    #[staticmethod]
    fn close(start: u64, end: u64) -> Self {
        Self::wrap(Event::Close { span: start..end })
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.event {
            Event::Open { .. } => "open",
            Event::Atom { .. } => "atom",
            Event::Close { .. } => "close",
        }
    }

    #[getter]
    fn span(&self) -> (u64, u64) {
        let span = match &self.event {
            Event::Open { span } | Event::Atom { span, .. } | Event::Close { span } => span,
        };
        (span.start, span.end)
    }

    #[getter]
    fn value(&self) -> Option<PySExprAtom> {
        match &self.event {
            Event::Atom { value, .. } => Some(PySExprAtom::wrap(value.clone())),
            Event::Open { .. } | Event::Close { .. } => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("Event(kind='{}', span={:?})", self.kind(), self.span())
    }
}

/// An immutable owned S-expression.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "SExpr"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PySExpr {
    expression: Expr,
}

impl PySExpr {
    fn wrap(expression: Expr) -> Self {
        Self { expression }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySExpr {
    #[staticmethod]
    #[pyo3(signature = (atom, start=0, end=0))]
    fn atom(atom: PyRef<'_, PySExprAtom>, start: u64, end: u64) -> Self {
        Self::wrap(Expr::atom(atom.atom.clone(), start..end))
    }

    #[staticmethod]
    #[pyo3(signature = (items, open=(0, 0), close=(0, 0)))]
    fn list(items: Vec<PyRef<'_, Self>>, open: (u64, u64), close: (u64, u64)) -> Self {
        Self::wrap(Expr::list(
            open.0..open.1,
            items
                .iter()
                .map(|item| item.expression.clone())
                .collect::<Vec<_>>(),
            close.0..close.1,
        ))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.expression.node() {
            ExprKind::Atom(_) => "atom",
            ExprKind::List(_) => "list",
        }
    }

    #[getter]
    fn atom_value(&self) -> Option<PySExprAtom> {
        match self.expression.node() {
            ExprKind::Atom(node) => Some(PySExprAtom::wrap(SpannedRepr::atom(node).clone())),
            ExprKind::List(_) => None,
        }
    }

    #[getter]
    fn span(&self) -> (u64, u64) {
        match self.expression.node() {
            ExprKind::Atom(node) => {
                let span = SpannedRepr::atom_meta(node);
                (span.start, span.end)
            }
            ExprKind::List(node) => {
                let span = SpannedRepr::list_meta(node);
                (span.open.start, span.close.end)
            }
        }
    }

    #[getter]
    fn open_span(&self) -> Option<(u64, u64)> {
        match self.expression.node() {
            ExprKind::List(node) => {
                let span = SpannedRepr::list_meta(node);
                Some((span.open.start, span.open.end))
            }
            ExprKind::Atom(_) => None,
        }
    }

    #[getter]
    fn close_span(&self) -> Option<(u64, u64)> {
        match self.expression.node() {
            ExprKind::List(node) => {
                let span = SpannedRepr::list_meta(node);
                Some((span.close.start, span.close.end))
            }
            ExprKind::Atom(_) => None,
        }
    }

    #[getter]
    fn items(&self, python: Python<'_>) -> PyResult<Py<PyTuple>> {
        let values = match self.expression.node() {
            ExprKind::List(node) => SpannedRepr::list_items(node)
                .iter()
                .cloned()
                .map(PySExpr::wrap)
                .map(|item| Py::new(python, item))
                .collect::<PyResult<Vec<_>>>()?,
            ExprKind::Atom(_) => Vec::new(),
        };
        Ok(PyTuple::new(python, values)?.unbind())
    }

    fn events(&self) -> Vec<PySExprEvent> {
        self.expression.events().map(PySExprEvent::wrap).collect()
    }

    /// Returns an immutable tree with all source positions removed.
    fn erase(&self) -> PyErasedSExpr {
        PyErasedSExpr::wrap(self.expression.erase())
    }

    fn __repr__(&self) -> String {
        format!("SExpr(kind='{}')", self.kind())
    }
}

/// An immutable S-expression without source positions.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "ErasedSExpr"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyErasedSExpr {
    expression: SExpr,
}

impl PyErasedSExpr {
    fn wrap(expression: SExpr) -> Self {
        Self { expression }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyErasedSExpr {
    #[staticmethod]
    fn atom(atom: PyRef<'_, PySExprAtom>) -> Self {
        Self::wrap(SExpr::<ErasedRepr>::atom(atom.atom.clone()))
    }

    #[staticmethod]
    fn list(items: Vec<PyRef<'_, Self>>) -> Self {
        Self::wrap(SExpr::<ErasedRepr>::list(
            items
                .iter()
                .map(|item| item.expression.clone())
                .collect::<Vec<_>>(),
        ))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.expression.node() {
            SExprNode::Atom(_) => "atom",
            SExprNode::List(_) => "list",
        }
    }

    #[getter]
    fn atom_value(&self) -> Option<PySExprAtom> {
        match self.expression.node() {
            SExprNode::Atom(node) => Some(PySExprAtom::wrap(ErasedRepr::atom(node).clone())),
            SExprNode::List(_) => None,
        }
    }

    #[getter]
    fn items(&self, python: Python<'_>) -> PyResult<Py<PyTuple>> {
        let values = match self.expression.node() {
            SExprNode::List(node) => ErasedRepr::list_items(node)
                .iter()
                .cloned()
                .map(Self::wrap)
                .map(|item| Py::new(python, item))
                .collect::<PyResult<Vec<_>>>()?,
            SExprNode::Atom(_) => Vec::new(),
        };
        Ok(PyTuple::new(python, values)?.unbind())
    }

    fn __repr__(&self) -> String {
        format!("ErasedSExpr(kind='{}')", self.kind())
    }
}

/// An immutable document containing zero or more S-expressions.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "Document"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PySExprDocument {
    document: Document,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySExprDocument {
    #[staticmethod]
    fn from_events(events: Vec<PyRef<'_, PySExprEvent>>) -> PyResult<Self> {
        let events = events.iter().map(|event| event.event.clone());
        Document::from_events(events)
            .map(|document| Self { document })
            .map_err(value_error)
    }

    #[getter]
    fn expressions(&self, python: Python<'_>) -> PyResult<Py<PyTuple>> {
        let expressions = self
            .document
            .expressions()
            .iter()
            .cloned()
            .map(PySExpr::wrap)
            .map(|expression| Py::new(python, expression))
            .collect::<PyResult<Vec<_>>>()?;
        Ok(PyTuple::new(python, expressions)?.unbind())
    }

    fn events(&self) -> Vec<PySExprEvent> {
        self.document.events().map(PySExprEvent::wrap).collect()
    }

    /// Returns a document with all source positions removed.
    fn erase(&self) -> PyErasedSExprDocument {
        PyErasedSExprDocument {
            document: self.document.erase(),
        }
    }

    fn __len__(&self) -> usize {
        self.document.expressions().len()
    }

    fn __repr__(&self) -> String {
        format!("Document(expressions={})", self.__len__())
    }
}

/// An immutable document of S-expressions without source positions.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.sexpr",
    name = "ErasedDocument"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyErasedSExprDocument {
    document: SDocument,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyErasedSExprDocument {
    #[new]
    fn new(expressions: Vec<PyRef<'_, PyErasedSExpr>>) -> Self {
        Self {
            document: SDocument::new(
                expressions
                    .iter()
                    .map(|expression| expression.expression.clone())
                    .collect::<Vec<_>>(),
            ),
        }
    }

    #[getter]
    fn expressions(&self, python: Python<'_>) -> PyResult<Py<PyTuple>> {
        let expressions = self
            .document
            .expressions()
            .iter()
            .cloned()
            .map(PyErasedSExpr::wrap)
            .map(|expression| Py::new(python, expression))
            .collect::<PyResult<Vec<_>>>()?;
        Ok(PyTuple::new(python, expressions)?.unbind())
    }

    fn __len__(&self) -> usize {
        self.document.expressions().len()
    }

    fn __repr__(&self) -> String {
        format!("ErasedDocument(expressions={})", self.__len__())
    }
}

#[pyfunction(name = "sexpr_parse")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn parse_document(source: &str) -> PyResult<PySExprDocument> {
    parse(source)
        .map(|document| PySExprDocument { document })
        .map_err(value_error)
}

#[pyfunction(name = "sexpr_parse_one")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn parse_expression(source: &str) -> PyResult<PySExpr> {
    parse_one(source).map(PySExpr::wrap).map_err(value_error)
}

#[pyfunction(name = "sexpr_parse_events")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn parse_events(source: &str) -> PyResult<Vec<PySExprEvent>> {
    covalence_data_sexpr::Parser::new(source)
        .map(|event| event.map(PySExprEvent::wrap).map_err(value_error))
        .collect()
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PySExprAtom>()?;
    module.add_class::<PySExprEvent>()?;
    module.add_class::<PySExpr>()?;
    module.add_class::<PyErasedSExpr>()?;
    module.add_class::<PySExprDocument>()?;
    module.add_class::<PyErasedSExprDocument>()?;
    module.add_function(wrap_pyfunction!(parse_document, module)?)?;
    module.add_function(wrap_pyfunction!(parse_expression, module)?)?;
    module.add_function(wrap_pyfunction!(parse_events, module)?)
}
