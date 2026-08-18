//! Indexed `HolE` arenas at the Python boundary.

#![allow(clippy::needless_pass_by_value)]
#![allow(clippy::trivially_copy_pass_by_ref)]

use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::{PyBytes, PyType};
use covalence_logic_hol::{
    Arena, Ctx, Expr, Format, INIT_ARENA, ImportTable, Ix, LinkRef, ObjectKind, Relation, SRef,
    Segment, Seq, SharedArena, SharedImportTable, SharedSeq, SurfaceTag, deserialize_cbor,
    serialize_cbor,
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

fn parse_relation(value: &str) -> PyResult<Relation> {
    match value {
        "syn_eq" => Ok(Relation::SynEq),
        "conv_eq" => Ok(Relation::ConvEq),
        "ty_eq" => Ok(Relation::TyEq),
        "has_ty" => Ok(Relation::HasTy),
        "imp" => Ok(Relation::Imp),
        "eq" => Ok(Relation::Eq),
        "has_kind" => Ok(Relation::HasKind),
        "ne" => Ok(Relation::Ne),
        _ => Err(PyValueError::new_err("unsupported HolE relation")),
    }
}

fn sref(value: i32) -> PyResult<SRef> {
    SRef::from_raw(value).map_err(value_error)
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
        self.segment.start.get()
    }
    #[getter]
    fn end(&self) -> u32 {
        self.segment.end.get()
    }
    #[getter]
    fn link(&self) -> PyLinkRef {
        PyLinkRef {
            link: self.segment.link,
        }
    }
    #[getter]
    fn source_start(&self) -> u32 {
        self.segment.source_start.get()
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

/// One immutable arena definition in the uniform `tag`/`ix`/`var` shape.
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
    #[pyo3(signature = (tag, ix=Vec::new(), var=None, value=None, data=None))]
    fn new(
        tag: &str,
        ix: Vec<u32>,
        var: Option<u32>,
        value: Option<bool>,
        data: Option<&Bound<'_, PyBytes>>,
    ) -> PyResult<Self> {
        let tag: SurfaceTag = tag.parse().map_err(value_error)?;
        let children = ix
            .into_iter()
            .map(Ix::new)
            .collect::<Result<Vec<_>, _>>()
            .map_err(value_error)?;
        Expr::from_parts(
            tag,
            &children,
            var,
            value,
            data.map(PyBytesMethods::as_bytes),
        )
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
            Expr::TyBv { index } | Expr::TmBv { index } => Some(index),
            Expr::TmFv { name, .. } => Some(name),
            _ => None,
        }
    }

    #[getter]
    fn value(&self) -> Option<bool> {
        match self.expr {
            Expr::TmBool { value } => Some(value),
            _ => None,
        }
    }

    #[getter]
    fn data(&self, python: Python<'_>) -> Option<Py<PyBytes>> {
        match &self.expr {
            Expr::TmNat { value } => {
                Some(PyBytes::new(python, &value.to_canonical_bytes()).unbind())
            }
            Expr::TmBytes { value } => Some(PyBytes::new(python, value).unbind()),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        if let Expr::TmNat { value } = &self.expr {
            return format!("Expr(tag='TM_NAT', data={:?})", value.to_canonical_bytes());
        }
        if let Expr::TmBytes { value } = &self.expr {
            return format!("Expr(tag='TM_BYTES', data={value:?})");
        }
        match (self.var(), self.value()) {
            (Some(var), None) => {
                format!("Expr(tag='{}', ix={:?}, var={var})", self.tag(), self.ix())
            }
            (None, Some(value)) => format!(
                "Expr(tag='{}', ix={:?}, value={value})",
                self.tag(),
                self.ix()
            ),
            (None, None) => format!("Expr(tag='{}', ix={:?})", self.tag(), self.ix()),
            (Some(_), Some(_)) => unreachable!("validated expression payload"),
        }
    }
}

/// Mutable owned arena. Decoding always returns this representation even when
/// the producer used a static slice-backed arena.
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

    #[classmethod]
    fn init(_class: &Bound<'_, PyType>) -> Self {
        Self {
            arena: INIT_ARENA
                .to_owned()
                .expect("audited static initialization arena"),
        }
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

/// One heterogeneous logical side of a sequent.
#[pyclass(skip_from_py_object, module = "covalence.logic.hol", name = "Ctx")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyCtx {
    ctx: Ctx,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCtx {
    #[new]
    #[pyo3(signature = (arena=None, imports=None))]
    fn new(arena: Option<&PyLinkRef>, imports: Option<PyRef<'_, PyO256>>) -> Self {
        Self {
            ctx: Ctx::new(
                arena.map(|link| link.link),
                imports.as_ref().map(PyO256::value),
            ),
        }
    }

    #[classmethod]
    fn from_cbor(_class: &Bound<'_, PyType>, bytes: Bytes) -> PyResult<Self> {
        deserialize_cbor(bytes.as_slice())
            .map(|ctx| Self { ctx })
            .map_err(value_error)
    }

    fn to_cbor<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = serialize_cbor(&self.ctx).map_err(value_error)?;
        Ok(PyBytes::new(python, &bytes))
    }

    fn insert_sequent(&mut self, sequent: &PyLinkRef) -> bool {
        self.ctx.insert_sequent(sequent.link)
    }

    fn insert(&mut self, relation: &str, left: i32, right: i32) -> PyResult<bool> {
        Ok(self
            .ctx
            .insert(parse_relation(relation)?, sref(left)?, sref(right)?))
    }

    fn insert_symmetric(&mut self, relation: &str, left: i32, right: i32) -> PyResult<bool> {
        let relation = parse_relation(relation)?;
        if !relation.is_symmetric() {
            return Err(PyValueError::new_err(
                "directional relation is not symmetric",
            ));
        }
        Ok(self
            .ctx
            .insert_symmetric(relation, sref(left)?, sref(right)?))
    }

    fn contains(&self, relation: &str, left: i32, right: i32) -> PyResult<bool> {
        Ok(self
            .ctx
            .contains(parse_relation(relation)?, sref(left)?, sref(right)?))
    }

    fn pairs(&self, relation: &str) -> PyResult<Vec<(i32, i32)>> {
        Ok(self
            .ctx
            .pairs(parse_relation(relation)?)
            .map(|(left, right)| (left.raw(), right.raw()))
            .collect())
    }

    #[getter]
    fn arena(&self) -> Option<PyLinkRef> {
        self.ctx.arena().map(|link| PyLinkRef { link })
    }

    #[getter]
    fn imports(&self, python: Python<'_>) -> PyResult<Option<Py<PyO256>>> {
        self.ctx
            .imports()
            .map(|address| py_hash(python, address))
            .transpose()
    }

    #[getter]
    fn sequents(&self) -> Vec<PyLinkRef> {
        self.ctx.sequents().map(|link| PyLinkRef { link }).collect()
    }
}

#[pyclass(module = "covalence.logic.hol", name = "Seq")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PySeq {
    seq: Seq,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySeq {
    #[new]
    #[pyo3(signature = (arena=None, imports=None))]
    fn new(arena: Option<&PyLinkRef>, imports: Option<PyRef<'_, PyO256>>) -> Self {
        Self {
            seq: Seq::new(
                arena.map(|link| link.link),
                imports.as_ref().map(PyO256::value),
            ),
        }
    }

    #[classmethod]
    fn from_cbor(_class: &Bound<'_, PyType>, bytes: Bytes) -> PyResult<Self> {
        deserialize_cbor(bytes.as_slice())
            .map(|seq| Self { seq })
            .map_err(value_error)
    }

    fn assume(&mut self, sequent: &PyLinkRef) -> bool {
        self.seq.assume(sequent.link)
    }

    fn conclude(&mut self, sequent: &PyLinkRef) -> bool {
        self.seq.conclude(sequent.link)
    }

    fn insert_premise(&mut self, relation: &str, left: i32, right: i32) -> PyResult<bool> {
        Ok(self.seq.relations_mut().insert_premise(
            parse_relation(relation)?,
            sref(left)?,
            sref(right)?,
        ))
    }

    fn insert_conclusion(&mut self, relation: &str, left: i32, right: i32) -> PyResult<bool> {
        Ok(self.seq.relations_mut().insert_conclusion(
            parse_relation(relation)?,
            sref(left)?,
            sref(right)?,
        ))
    }

    fn premise_pairs(&self, relation: &str) -> PyResult<Vec<(i32, i32)>> {
        Ok(self
            .seq
            .relations()
            .premise_pairs(parse_relation(relation)?)
            .map(|(left, right)| (left.raw(), right.raw()))
            .collect())
    }

    fn conclusion_pairs(&self, relation: &str) -> PyResult<Vec<(i32, i32)>> {
        Ok(self
            .seq
            .relations()
            .conclusion_pairs(parse_relation(relation)?)
            .map(|(left, right)| (left.raw(), right.raw()))
            .collect())
    }

    #[getter]
    fn premises(&self) -> PyCtx {
        PyCtx {
            ctx: self.seq.premises(),
        }
    }

    #[getter]
    fn conclusion(&self) -> PyCtx {
        PyCtx {
            ctx: self.seq.conclusion(),
        }
    }

    #[classmethod]
    fn from_premises(_class: &Bound<'_, PyType>, premises: &PyCtx) -> Self {
        Self {
            seq: Seq::from_premises(premises.ctx.clone()),
        }
    }

    #[classmethod]
    fn from_conclusion(_class: &Bound<'_, PyType>, conclusion: &PyCtx) -> Self {
        Self {
            seq: Seq::from_conclusion(conclusion.ctx.clone()),
        }
    }

    #[classmethod]
    fn from_contexts(
        _class: &Bound<'_, PyType>,
        premises: &PyCtx,
        conclusion: &PyCtx,
    ) -> PyResult<Self> {
        Seq::from_contexts(premises.ctx.clone(), conclusion.ctx.clone())
            .map(|seq| Self { seq })
            .ok_or_else(|| PyValueError::new_err("contexts use different arenas or import tables"))
    }

    fn to_cbor<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = serialize_cbor(&self.seq).map_err(value_error)?;
        Ok(PyBytes::new(python, &bytes))
    }

    fn address(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        let seq = SharedSeq::new(self.seq.clone()).map_err(value_error)?;
        py_hash(python, seq.address())
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyExpr>()?;
    module.add_class::<PyLinkRef>()?;
    module.add_class::<PySegment>()?;
    module.add_class::<PyImportTable>()?;
    module.add_class::<PyArena>()?;
    module.add_class::<PyCtx>()?;
    module.add_class::<PySeq>()
}
