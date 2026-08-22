//! The one-based Ethane arena and checked kernel at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

use covalence_data_cas::MemoryCas;
use covalence_lib_hash::O256;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{types::PyBytes, types::PyType};
use covalence_logic_hol::{
    Arena, Import, ImportId, Kernel, KindIx, Link, LinkFormat, Meta, Ref, Sort, TmIx, TyIx,
    cas::CasResolver, wire,
};

use crate::hash::PyO256;

type Resolver = CasResolver<MemoryCas>;

fn value_error(error: impl ToString) -> PyErr {
    PyValueError::new_err(error.to_string())
}

fn reference(value: u64) -> PyResult<Ref> {
    Ref::new(value).ok_or_else(|| PyValueError::new_err("references are one-based"))
}

fn source(value: u64) -> PyResult<ImportId> {
    ImportId::new(value).ok_or_else(|| PyValueError::new_err("import IDs are one-based"))
}

fn allocated(value: Option<Ref>) -> PyResult<u64> {
    value
        .map(Ref::get)
        .ok_or_else(|| PyValueError::new_err("arena reference space is exhausted"))
}

fn imported(value: Option<ImportId>) -> PyResult<u64> {
    value
        .map(ImportId::get)
        .ok_or_else(|| PyValueError::new_err("arena import space is exhausted"))
}

fn sort_name(sort: Sort) -> &'static str {
    match sort {
        Sort::Kind => "kind",
        Sort::Ty => "ty",
        Sort::Tm => "tm",
    }
}

/// A content-addressed Ethane arena link.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolLink"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyLink(Link);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyLink {
    #[new]
    fn new(address: PyRef<'_, PyO256>) -> Self {
        Self(Link {
            format: LinkFormat::Cbor,
            blake3: PyO256::value(&address),
        })
    }

    #[getter]
    fn format(&self) -> &'static str {
        match self.0.format {
            LinkFormat::Cbor => "cbor",
        }
    }

    #[getter]
    fn blake3(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.blake3)
    }
}

/// An immutable snapshot of one private Ethane row.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolDefinition"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyDefinition {
    reference: u64,
    tag: &'static str,
    children: Vec<u64>,
    name: Option<u64>,
    value: Option<bool>,
    source: Option<u64>,
    foreign: Option<u64>,
    equal: Option<u64>,
    classifier: Option<u64>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyDefinition {
    #[getter]
    const fn reference(&self) -> u64 {
        self.reference
    }

    #[getter]
    const fn tag(&self) -> &'static str {
        self.tag
    }

    #[getter]
    fn children(&self) -> Vec<u64> {
        self.children.clone()
    }

    #[getter]
    const fn name(&self) -> Option<u64> {
        self.name
    }

    #[getter]
    const fn value(&self) -> Option<bool> {
        self.value
    }

    #[getter]
    const fn source(&self) -> Option<u64> {
        self.source
    }

    #[getter]
    const fn foreign(&self) -> Option<u64> {
        self.foreign
    }

    #[getter]
    const fn equal(&self) -> Option<u64> {
        self.equal
    }

    #[getter]
    const fn classifier(&self) -> Option<u64> {
        self.classifier
    }
}

/// An immutable snapshot of one metadata premise or conclusion.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolMeta"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyMeta(Meta);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyMeta {
    #[getter]
    fn tag(&self) -> &'static str {
        match self.0 {
            Meta::Valid { .. } => "meta.valid",
            Meta::Wf { .. } => "meta.wf",
        }
    }

    #[getter]
    fn source(&self) -> u64 {
        match self.0 {
            Meta::Valid { src } | Meta::Wf { src, .. } => src.get(),
        }
    }

    #[getter]
    fn reference(&self) -> Option<u64> {
        match self.0 {
            Meta::Valid { .. } => None,
            Meta::Wf { ix, .. } => Some(ix.get()),
        }
    }

    #[getter]
    fn classifier(&self) -> Option<u64> {
        match self.0 {
            Meta::Valid { .. } => None,
            Meta::Wf { sort, .. } => Some(sort.get()),
        }
    }
}

/// A mutable, unvalidated one-based dense Ethane arena.
#[pyclass(skip_from_py_object, module = "covalence.logic.hol", name = "HolArena")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Default)]
pub struct PyArena {
    arena: Arena,
}

impl PyArena {
    fn definition_at(&self, reference: Ref) -> Option<PyDefinition> {
        let tag = self.arena.tag(reference)?;
        let (source, foreign) = self
            .arena
            .foreign(reference)
            .map_or((None, None), |(source, foreign)| {
                (Some(source.get()), Some(foreign.get()))
            });
        Some(PyDefinition {
            reference: reference.get(),
            tag: tag.name(),
            children: self.arena.children(reference)?.map(Ref::get).collect(),
            name: self.arena.name(reference),
            value: self.arena.bool_value(reference),
            source,
            foreign,
            equal: self.arena.eq(reference).map(Ref::get),
            classifier: self.arena.sort(reference).map(Ref::get),
        })
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyArena {
    #[new]
    fn new() -> Self {
        Self::default()
    }

    #[classmethod]
    fn from_cbor(_class: &Bound<'_, PyType>, bytes: Bytes) -> PyResult<Self> {
        Ok(Self {
            arena: wire::deserialize(bytes.as_slice()).map_err(value_error)?,
        })
    }

    fn to_cbor<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let mut bytes = Vec::new();
        wire::serialize(&self.arena, &mut bytes).map_err(value_error)?;
        Ok(PyBytes::new(python, &bytes))
    }

    fn address(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        let mut bytes = Vec::new();
        wire::serialize(&self.arena, &mut bytes).map_err(value_error)?;
        PyO256::wrap(python, O256::from_bytes(&bytes))
    }

    fn definition(&self, reference_value: u64) -> PyResult<Option<PyDefinition>> {
        Ok(self.definition_at(reference(reference_value)?))
    }

    #[getter]
    fn definitions(&self) -> PyResult<Vec<PyDefinition>> {
        (1..=self.arena.len())
            .map(|position| {
                let value = u64::try_from(position).map_err(value_error)?;
                self.definition_at(reference(value)?)
                    .ok_or_else(|| PyValueError::new_err("arena definition is missing"))
            })
            .collect()
    }

    #[getter]
    fn imports(&self, python: Python<'_>) -> PyResult<Vec<Py<PyAny>>> {
        self.arena
            .imports()
            .iter()
            .map(|entry| match entry {
                Import::Null => Ok(python.None()),
                Import::Literal(arena) => Py::new(
                    python,
                    Self {
                        arena: (**arena).clone(),
                    },
                )
                .map(Py::into_any),
                Import::Link(link) => Py::new(python, PyLink(*link)).map(Py::into_any),
            })
            .collect()
    }

    #[getter]
    fn axioms(&self) -> Vec<String> {
        self.arena.axioms().map(str::to_owned).collect()
    }

    #[getter]
    fn context(&self) -> Vec<u64> {
        self.arena.context().map(Ref::get).collect()
    }

    #[getter]
    fn assumptions(&self) -> Vec<PyMeta> {
        self.arena
            .assumptions()
            .iter()
            .copied()
            .map(PyMeta)
            .collect()
    }

    #[getter]
    fn assertions(&self) -> Vec<PyMeta> {
        self.arena
            .assertions()
            .iter()
            .copied()
            .map(PyMeta)
            .collect()
    }

    fn add_null_import(&mut self) -> PyResult<u64> {
        imported(self.arena.push_import(Import::Null))
    }

    fn add_literal_import(&mut self, arena: &Self) -> PyResult<u64> {
        imported(
            self.arena
                .push_import(Import::Literal(Box::new(arena.arena.clone()))),
        )
    }

    fn add_link_import(&mut self, link: &PyLink) -> PyResult<u64> {
        imported(self.arena.push_import(Import::Link(link.0)))
    }

    fn add_axiom(&mut self, name: &str) {
        self.arena.insert_axiom(name);
    }

    fn add_context(&mut self, reference_value: u64) -> PyResult<()> {
        self.arena.insert_context(reference(reference_value)?);
        Ok(())
    }

    fn assume_valid(&mut self, source_value: u64) -> PyResult<()> {
        self.arena.push_assumption(Meta::Valid {
            src: source(source_value)?,
        });
        Ok(())
    }

    fn assert_valid(&mut self, source_value: u64) -> PyResult<()> {
        self.arena.push_assertion(Meta::Valid {
            src: source(source_value)?,
        });
        Ok(())
    }

    fn assume_wf(&mut self, source_value: u64, ix: u64, sort: u64) -> PyResult<()> {
        self.arena.push_assumption(Meta::Wf {
            src: source(source_value)?,
            ix: reference(ix)?,
            sort: reference(sort)?,
        });
        Ok(())
    }

    fn assert_wf(&mut self, source_value: u64, ix: u64, sort: u64) -> PyResult<()> {
        self.arena.push_assertion(Meta::Wf {
            src: source(source_value)?,
            ix: reference(ix)?,
            sort: reference(sort)?,
        });
        Ok(())
    }

    fn kind_star(&mut self) -> PyResult<u64> {
        allocated(self.arena.push_kind_star())
    }

    fn kind_arr(&mut self, domain: u64, codomain: u64) -> PyResult<u64> {
        let domain = reference(domain)?;
        let codomain = reference(codomain)?;
        allocated(self.arena.push_kind_arr(domain, codomain))
    }

    fn bool_ty(&mut self) -> PyResult<u64> {
        allocated(self.arena.push_bool_ty())
    }

    fn ty_arr(&mut self, domain: u64, codomain: u64) -> PyResult<u64> {
        let domain = reference(domain)?;
        let codomain = reference(codomain)?;
        allocated(self.arena.push_ty_arr(domain, codomain))
    }

    fn ty_app(&mut self, function: u64, argument: u64) -> PyResult<u64> {
        let function = reference(function)?;
        let argument = reference(argument)?;
        allocated(self.arena.push_ty_app(function, argument))
    }

    fn ty_lam(&mut self, binder: u64, body: u64) -> PyResult<u64> {
        let binder = reference(binder)?;
        let body = reference(body)?;
        allocated(self.arena.push_ty_lam(binder, body))
    }

    fn ty_fv(&mut self, name: u64, kind: u64) -> PyResult<u64> {
        let kind = reference(kind)?;
        allocated(self.arena.push_ty_fv(name, kind))
    }

    fn ty_exists(&mut self, name: u64, predicate: u64) -> PyResult<u64> {
        let predicate = reference(predicate)?;
        allocated(self.arena.push_ty_exists(name, predicate))
    }

    fn model(&mut self, name: u64, predicate: u64) -> PyResult<u64> {
        let predicate = reference(predicate)?;
        allocated(self.arena.push_model(name, predicate))
    }

    fn tm_fv(&mut self, name: u64, ty: u64) -> PyResult<u64> {
        let ty = reference(ty)?;
        allocated(self.arena.push_tm_fv(name, ty))
    }

    fn app(&mut self, function: u64, argument: u64) -> PyResult<u64> {
        let function = reference(function)?;
        let argument = reference(argument)?;
        allocated(self.arena.push_app(function, argument))
    }

    fn lam(&mut self, binder: u64, body: u64) -> PyResult<u64> {
        let binder = reference(binder)?;
        let body = reference(body)?;
        allocated(self.arena.push_lam(binder, body))
    }

    fn bool(&mut self, value: bool) -> PyResult<u64> {
        allocated(self.arena.push_bool(value))
    }

    fn tm_eq(&mut self, left: u64, right: u64) -> PyResult<u64> {
        let left = reference(left)?;
        let right = reference(right)?;
        allocated(self.arena.push_tm_eq(left, right))
    }

    fn eps(&mut self, ty: u64, predicate: u64) -> PyResult<u64> {
        let ty = reference(ty)?;
        let predicate = reference(predicate)?;
        allocated(self.arena.push_eps(ty, predicate))
    }

    fn tm_ref(&mut self, source_value: u64, foreign: u64) -> PyResult<u64> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_tm_ref(source, foreign))
    }

    fn ty_ref(&mut self, source_value: u64, foreign: u64) -> PyResult<u64> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_ty_ref(source, foreign))
    }

    fn kind_ref(&mut self, source_value: u64, foreign: u64) -> PyResult<u64> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_kind_ref(source, foreign))
    }

    fn __len__(&self) -> usize {
        self.arena.len()
    }
}

/// A resolver and retryable in-memory content-addressed store.
#[pyclass(module = "covalence.logic.hol", name = "HolSession")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PySession {
    resolver: Arc<Resolver>,
    fuel: usize,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySession {
    #[new]
    #[pyo3(signature = (fuel=256))]
    fn new(fuel: usize) -> Self {
        Self {
            resolver: Arc::new(Resolver::new(MemoryCas::new())),
            fuel,
        }
    }

    fn insert(&self, python: Python<'_>, bytes: Bytes) -> PyResult<Py<PyO256>> {
        let address = self
            .resolver
            .cas()
            .insert(bytes.as_slice().to_vec())
            .map_err(value_error)?;
        PyO256::wrap(python, address)
    }

    fn store(&self, python: Python<'_>, arena: &PyArena) -> PyResult<Py<PyO256>> {
        let mut bytes = Vec::new();
        wire::serialize(&arena.arena, &mut bytes).map_err(value_error)?;
        let address = self.resolver.cas().insert(bytes).map_err(value_error)?;
        PyO256::wrap(python, address)
    }

    fn contains(&self, address: PyRef<'_, PyO256>) -> bool {
        self.resolver.cas().contains(PyO256::value(&address))
    }

    fn resolve_sort(&self, arena: &PyArena, reference_value: u64) -> PyResult<&'static str> {
        let reference = reference(reference_value)?;
        arena
            .arena
            .resolve_sort(self.resolver.as_ref(), reference, self.fuel)
            .map(sort_name)
            .map_err(|error| value_error(format!("{error:?}")))
    }

    fn check(&self, arena: &PyArena) -> PyResult<PyKernel> {
        let kernel = Kernel::try_from_arena(arena.arena.clone(), self.resolver.as_ref(), self.fuel)
            .map_err(value_error)?;
        Ok(PyKernel {
            kernel,
            resolver: Arc::clone(&self.resolver),
            fuel: self.fuel,
            owner: NEXT_OWNER.fetch_add(1, Ordering::Relaxed),
        })
    }
}

static NEXT_OWNER: AtomicU64 = AtomicU64::new(1);

macro_rules! checked_handle {
    ($rust:ident, $python:literal, $index:ty) => {
        #[pyclass(
                                                            frozen,
                                                            skip_from_py_object,
                                                            module = "covalence.logic.hol",
                                                            name = $python,
                                                            crate = "covalence_lib_python::pyo3"
                                                        )]
        #[derive(Clone, Copy)]
        pub struct $rust {
            #[allow(dead_code)]
            owner: u64,
            index: $index,
        }

        #[pymethods]
        #[pyo3(crate = "covalence_lib_python::pyo3")]
        impl $rust {
            #[getter]
            fn reference(&self) -> u64 {
                self.index.reference().get()
            }
        }
    };
}

checked_handle!(PyKind, "HolKind", KindIx);
checked_handle!(PyTy, "HolTy", TyIx);
checked_handle!(PyTm, "HolTm", TmIx);

/// Evidence that one checked kernel contains the displayed equality claim.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolEquality"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyEquality {
    _owner: u64,
    left: TmIx,
    right: TmIx,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyEquality {
    #[getter]
    fn left(&self) -> u64 {
        self.left.reference().get()
    }

    #[getter]
    fn right(&self) -> u64 {
        self.right.reference().get()
    }
}

/// A checked Ethane arena. Instances are created only by `HolSession.check`.
#[pyclass(module = "covalence.logic.hol", name = "HolKernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel {
    kernel: Kernel,
    resolver: Arc<Resolver>,
    fuel: usize,
    owner: u64,
}

impl PyKernel {
    fn same(&self, owner: u64) -> PyResult<()> {
        if self.owner == owner {
            Ok(())
        } else {
            Err(PyValueError::new_err(
                "checked handles belong to a different kernel",
            ))
        }
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    #[getter]
    fn arena(&self) -> PyArena {
        PyArena {
            arena: self.kernel.arena().clone(),
        }
    }

    fn kind(&self, reference_value: u64) -> PyResult<PyKind> {
        let index = self
            .kernel
            .kind_at(
                self.resolver.as_ref(),
                self.fuel,
                reference(reference_value)?,
            )
            .map_err(value_error)?;
        Ok(PyKind {
            owner: self.owner,
            index,
        })
    }

    fn ty(&self, reference_value: u64) -> PyResult<PyTy> {
        let index = self
            .kernel
            .ty_at(
                self.resolver.as_ref(),
                self.fuel,
                reference(reference_value)?,
            )
            .map_err(value_error)?;
        Ok(PyTy {
            owner: self.owner,
            index,
        })
    }

    fn tm(&self, reference_value: u64) -> PyResult<PyTm> {
        let index = self
            .kernel
            .tm_at(
                self.resolver.as_ref(),
                self.fuel,
                reference(reference_value)?,
            )
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn star(&mut self) -> PyResult<PyKind> {
        let index = self
            .kernel
            .star(self.resolver.as_ref(), self.fuel)
            .map_err(value_error)?;
        Ok(PyKind {
            owner: self.owner,
            index,
        })
    }

    fn bool_ty(&mut self) -> PyResult<PyTy> {
        let index = self
            .kernel
            .bool_ty(self.resolver.as_ref(), self.fuel)
            .map_err(value_error)?;
        Ok(PyTy {
            owner: self.owner,
            index,
        })
    }

    fn tm_fv(&mut self, name: u64, ty: &PyTy) -> PyResult<PyTm> {
        self.same(ty.owner)?;
        let index = self
            .kernel
            .tm_fv(self.resolver.as_ref(), self.fuel, name, ty.index)
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn lam(&mut self, binder: &PyTm, body: &PyTm) -> PyResult<PyTm> {
        self.same(binder.owner)?;
        self.same(body.owner)?;
        let index = self
            .kernel
            .lam(self.resolver.as_ref(), self.fuel, binder.index, body.index)
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn app(&mut self, function: &PyTm, argument: &PyTm) -> PyResult<PyTm> {
        self.same(function.owner)?;
        self.same(argument.owner)?;
        let index = self
            .kernel
            .app(
                self.resolver.as_ref(),
                self.fuel,
                function.index,
                argument.index,
            )
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn eq(&mut self, left: &PyTm, right: &PyTm) -> PyResult<PyTm> {
        self.same(left.owner)?;
        self.same(right.owner)?;
        let index = self
            .kernel
            .eq(self.resolver.as_ref(), self.fuel, left.index, right.index)
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn bool(&mut self, value: bool) -> PyResult<PyTm> {
        let index = self
            .kernel
            .bool(self.resolver.as_ref(), self.fuel, value)
            .map_err(value_error)?;
        Ok(PyTm {
            owner: self.owner,
            index,
        })
    }

    fn assert_eq(&mut self, left: &PyTm, right: &PyTm) -> PyResult<PyEquality> {
        self.same(left.owner)?;
        self.same(right.owner)?;
        self.kernel
            .assert_eq(self.resolver.as_ref(), self.fuel, left.index, right.index)
            .map_err(value_error)?;
        Ok(PyEquality {
            _owner: self.owner,
            left: left.index,
            right: right.index,
        })
    }

    fn __len__(&self) -> usize {
        self.kernel.arena().len()
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyLink>()?;
    module.add_class::<PyDefinition>()?;
    module.add_class::<PyMeta>()?;
    module.add_class::<PyArena>()?;
    module.add_class::<PySession>()?;
    module.add_class::<PyKind>()?;
    module.add_class::<PyTy>()?;
    module.add_class::<PyTm>()?;
    module.add_class::<PyEquality>()?;
    module.add_class::<PyKernel>()
}
