//! Python access to indexed `HolE` syntax arenas.

#![allow(clippy::needless_pass_by_value)]
#![allow(clippy::trivially_copy_pass_by_ref)]

use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::{PyBytes, PyType};
use covalence_logic_hol::{
    Arena, Expr, Format, ImportTable, Ix, LinkRef, ObjectKind, Segment, SharedArena,
    SharedImportTable, SurfaceTag, deserialize_cbor, serialize_cbor,
};

use crate::hash::PyO256;

fn value_error(error: impl ToString) -> PyErr {
    PyValueError::new_err(error.to_string())
}

fn py_hash(python: Python<'_>, hash: covalence_lib_hash::O256) -> PyResult<Py<PyO256>> {
    PyO256::wrap(python, hash)
}

fn parse_format(value: &str) -> PyResult<Format> {
    match value {
        "blob" => Ok(Format::Blob),
        "cbor_dense" => Ok(Format::CborDense),
        "cbor_sparse" => Ok(Format::CborSparse),
        _ => Err(PyValueError::new_err("unsupported link format")),
    }
}

fn format_name(value: Format) -> &'static str {
    match value {
        Format::Blob => "blob",
        Format::CborDense => "cbor_dense",
        Format::CborSparse => "cbor_sparse",
    }
}

fn parse_kind(value: &str) -> PyResult<ObjectKind> {
    match value {
        "bytes" => Ok(ObjectKind::Bytes),
        "import_table" => Ok(ObjectKind::ImportTable),
        "arena" => Ok(ObjectKind::Arena),
        "sequent" => Ok(ObjectKind::Sequent),
        _ => Err(PyValueError::new_err("unsupported object kind")),
    }
}

fn kind_name(value: ObjectKind) -> &'static str {
    match value {
        ObjectKind::Bytes => "bytes",
        ObjectKind::ImportTable => "import_table",
        ObjectKind::Arena => "arena",
        ObjectKind::Sequent => "sequent",
    }
}

#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "LinkRef"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyLinkRef {
    link: LinkRef,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyLinkRef {
    #[new]
    fn new(import_id: u32, format: &str, kind: &str) -> PyResult<Self> {
        Ok(Self {
            link: LinkRef {
                import: import_id,
                format: parse_format(format)?,
                kind: parse_kind(kind)?,
            },
        })
    }

    #[getter]
    fn import_id(&self) -> u32 {
        self.link.import
    }

    #[getter]
    fn format(&self) -> &'static str {
        format_name(self.link.format)
    }

    #[getter]
    fn kind(&self) -> &'static str {
        kind_name(self.link.kind)
    }
}

#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "Segment"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PySegment {
    segment: Segment,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySegment {
    #[new]
    fn new(start: u32, end: u32, link: &PyLinkRef, source_start: u32) -> PyResult<Self> {
        Ok(Self {
            segment: Segment::new(
                Ix::new(start).map_err(value_error)?,
                Ix::new(end).map_err(value_error)?,
                link.link,
                Ix::new(source_start).map_err(value_error)?,
            )
            .map_err(value_error)?,
        })
    }

    #[getter]
    fn start(&self) -> u32 {
        self.segment.start().get()
    }

    #[getter]
    fn end(&self) -> u32 {
        self.segment.end().get()
    }

    #[getter]
    fn link(&self) -> PyLinkRef {
        PyLinkRef {
            link: self.segment.link(),
        }
    }

    #[getter]
    fn source_start(&self) -> u32 {
        self.segment.source_start().get()
    }
}

#[pyclass(module = "covalence.logic.hol", name = "ImportTable")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyImportTable {
    table: ImportTable,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyImportTable {
    #[new]
    fn new() -> Self {
        Self {
            table: ImportTable::new(),
        }
    }

    #[classmethod]
    fn from_cbor(_class: &Bound<'_, PyType>, bytes: Bytes) -> PyResult<Self> {
        deserialize_cbor(bytes.as_slice())
            .map(|table| Self { table })
            .map_err(value_error)
    }

    fn push(&mut self, address: PyRef<'_, PyO256>) -> PyResult<u32> {
        self.table
            .push(PyO256::value(&address))
            .map_err(value_error)
    }

    fn to_cbor<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = serialize_cbor(&self.table).map_err(value_error)?;
        Ok(PyBytes::new(python, &bytes))
    }

    fn address(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        let table = SharedImportTable::new(self.table.clone()).map_err(value_error)?;
        py_hash(python, table.address())
    }

    fn __len__(&self) -> usize {
        self.table.iter().count()
    }
}

/// One immutable definition in the arena's `tag`/`ix`/`var` wire shape.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "Expr"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyExpr {
    expr: Expr,
}

impl From<Expr> for PyExpr {
    fn from(expr: Expr) -> Self {
        Self { expr }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyExpr {
    #[new]
    #[pyo3(signature = (tag, ix=Vec::new(), var=None))]
    fn new(tag: &str, ix: Vec<u32>, var: Option<u32>) -> PyResult<Self> {
        let tag: SurfaceTag = tag.parse().map_err(value_error)?;
        let children = ix
            .into_iter()
            .map(Ix::new)
            .collect::<Result<Vec<_>, _>>()
            .map_err(value_error)?;
        Expr::from_parts(tag, &children, var)
            .map(Self::from)
            .map_err(value_error)
    }

    #[getter]
    fn tag(&self) -> &'static str {
        self.expr.tag().into()
    }

    #[getter]
    fn ix(&self) -> Vec<u32> {
        self.expr.children().map(Ix::get).collect()
    }

    #[getter]
    fn var(&self) -> Option<u32> {
        match self.expr {
            Expr::TyBv { index } => Some(index),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        match self.var() {
            Some(var) => format!("Expr(tag='{}', ix=[], var={var})", self.tag()),
            None => format!("Expr(tag='{}', ix={:?})", self.tag(), self.ix()),
        }
    }
}

/// Mutable, owned syntax arena.
#[pyclass(module = "covalence.logic.hol", name = "Arena")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyArena {
    arena: Arena,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyArena {
    #[new]
    #[pyo3(signature = (imports=None))]
    fn new(imports: Option<PyRef<'_, PyO256>>) -> Self {
        Self {
            arena: Arena::new(imports.as_ref().map(PyO256::value)),
        }
    }

    #[classmethod]
    fn from_cbor(_class: &Bound<'_, PyType>, bytes: Bytes) -> PyResult<Self> {
        deserialize_cbor(bytes.as_slice())
            .map(|arena| Self { arena })
            .map_err(value_error)
    }

    fn to_cbor<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = serialize_cbor(&self.arena).map_err(value_error)?;
        Ok(PyBytes::new(python, &bytes))
    }

    fn push(&mut self, expr: &PyExpr) -> PyResult<u32> {
        self.arena
            .push(expr.expr.clone())
            .map(Ix::get)
            .map_err(value_error)
    }

    fn add_segment(&mut self, segment: &PySegment) -> PyResult<()> {
        self.arena.add_segment(segment.segment).map_err(value_error)
    }

    fn address(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        let arena = SharedArena::new(self.arena.clone()).map_err(value_error)?;
        py_hash(python, arena.address())
    }

    fn __len__(&self) -> usize {
        self.arena.defs().len()
    }

    #[getter]
    fn local_base(&self) -> u32 {
        self.arena.local_base()
    }

    #[getter]
    fn defs(&self) -> Vec<PyExpr> {
        self.arena
            .defs()
            .iter()
            .cloned()
            .map(PyExpr::from)
            .collect()
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyExpr>()?;
    module.add_class::<PyLinkRef>()?;
    module.add_class::<PySegment>()?;
    module.add_class::<PyImportTable>()?;
    module.add_class::<PyArena>()
}
