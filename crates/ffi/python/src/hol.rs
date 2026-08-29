//! The one-based Ethane arena and checked kernel at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use std::{
    num::NonZeroU64,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
};

use covalence_data_cas::{AsyncCas, AsyncCasError, Bytes as CasBytes, CasFuture};
use covalence_lib_hash::O256;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    exceptions::PyRuntimeError,
    types::{PyBool, PyBytes, PyType},
};
use covalence_logic_hol::{
    AmbPred, Arena, CnfId, DnfId, Import, ImportId, Kernel, Link, LinkFormat, Lit, LitVec, Ref,
    Sort, SynFact, SynFactId, SynRel, ThmId,
    builtin::{Op1, Op2},
    wire,
};

use crate::hash::PyO256;

fn value_error(error: impl ToString) -> PyErr {
    PyValueError::new_err(error.to_string())
}

fn reference(value: i32) -> PyResult<Ref> {
    Ref::new(value).ok_or_else(|| PyValueError::new_err("references are one-based"))
}

fn source(value: i32) -> PyResult<ImportId> {
    ImportId::new(value).ok_or_else(|| PyValueError::new_err("import IDs are one-based"))
}

fn fact_id(value: i32) -> PyResult<SynFactId> {
    SynFactId::new(value).ok_or_else(|| PyValueError::new_err("fact IDs are one-based"))
}

fn push_amb_ctx(arena: &mut Arena, predicate: AmbPred) -> PyResult<()> {
    if arena.push_ambient_context(predicate) {
        Ok(())
    } else {
        Err(PyRuntimeError::new_err(
            "ambient predicate storage is exhausted",
        ))
    }
}

fn push_amb_thm(arena: &mut Arena, predicate: AmbPred) -> PyResult<()> {
    if arena.push_ambient_theorem(predicate) {
        Ok(())
    } else {
        Err(PyRuntimeError::new_err(
            "ambient theorem storage is exhausted",
        ))
    }
}

fn classical_rows(arena: &covalence_logic_hol::ClassicalArena) -> Vec<PySequent> {
    arena
        .live_theorems()
        .map(|theorem| {
            (
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
            )
        })
        .collect()
}

fn fact_target(value: Option<i32>) -> PyResult<Option<SynFactId>> {
    value.map(fact_id).transpose()
}

fn theorem_id(value: i32) -> PyResult<ThmId> {
    ThmId::new(value).ok_or_else(|| PyValueError::new_err("theorem IDs are positive i32 values"))
}

fn cnf_id(value: i32) -> PyResult<CnfId> {
    CnfId::new(value).ok_or_else(|| PyValueError::new_err("CNF row IDs are positive i32 values"))
}

fn dnf_id(value: i32) -> PyResult<DnfId> {
    DnfId::new(value).ok_or_else(|| PyValueError::new_err("DNF row IDs are positive i32 values"))
}

fn literal(value: i32) -> PyResult<Lit> {
    Lit::try_new(value).map_err(value_error)
}

fn literals(values: Vec<i32>) -> PyResult<Vec<Lit>> {
    values.into_iter().map(literal).collect()
}

fn matrix(values: Vec<Vec<i32>>) -> PyResult<Vec<LitVec>> {
    values
        .into_iter()
        .map(|row| {
            literals(row)
                .map(IntoIterator::into_iter)
                .map(Iterator::collect)
        })
        .collect()
}

// The CBOR decoder's recursion budget admits 126 nested arena imports. Keeping
// construction one level below its 127-container limit guarantees that every
// arena accepted here can be decoded again.
const MAX_LITERAL_IMPORT_DEPTH: usize = 126;

fn ensure_literal_import_can_be_wrapped(arena: &Arena) -> PyResult<()> {
    let mut pending = vec![(arena, 0_usize)];
    while let Some((current, depth)) = pending.pop() {
        if depth >= MAX_LITERAL_IMPORT_DEPTH {
            return Err(PyValueError::new_err(format!(
                "literal imports may nest at most {MAX_LITERAL_IMPORT_DEPTH} levels"
            )));
        }
        pending.extend(current.imports().iter().filter_map(|import| match import {
            Import::Literal(child) => Some((child.as_ref(), depth + 1)),
            Import::Null | Import::Link(_) => None,
        }));
    }
    Ok(())
}

fn parse_relation(value: &str) -> PyResult<SynRel> {
    match value {
        "syn" => Ok(SynRel::Syn),
        "alpha" => Ok(SynRel::Alpha),
        "conv" => Ok(SynRel::Conv),
        _ => Err(PyValueError::new_err(
            "relation must be 'syn', 'alpha', or 'conv'",
        )),
    }
}

const fn relation_name(value: SynRel) -> &'static str {
    match value {
        SynRel::Syn => "syn",
        SynRel::Alpha => "alpha",
        SynRel::Conv => "conv",
    }
}

fn allocated(value: Option<Ref>) -> PyResult<i32> {
    value
        .map(Ref::get)
        .ok_or_else(|| PyValueError::new_err("arena reference space is exhausted"))
}

fn imported(value: Option<ImportId>) -> PyResult<i32> {
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
    reference: i32,
    tag: &'static str,
    children: Vec<i32>,
    name: Option<u64>,
    value: Option<bool>,
    source: Option<i32>,
    foreign: Option<i32>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyDefinition {
    #[getter]
    const fn reference(&self) -> i32 {
        self.reference
    }

    #[getter]
    const fn tag(&self) -> &'static str {
        self.tag
    }

    #[getter]
    fn children(&self) -> Vec<i32> {
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
    const fn source(&self) -> Option<i32> {
        self.source
    }

    #[getter]
    const fn foreign(&self) -> Option<i32> {
        self.foreign
    }
}

/// An immutable ambient predicate row.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "AmbPred"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyAmbPred(AmbPred);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyAmbPred {
    #[getter]
    fn tag(&self) -> &'static str {
        match self.0 {
            AmbPred::ArenaOk { .. } => "arena.ok",
            AmbPred::HolSort { .. } => "hol.sort",
        }
    }

    #[getter]
    fn source(&self) -> i32 {
        match self.0 {
            AmbPred::ArenaOk { src } | AmbPred::HolSort { src, .. } => src.get(),
        }
    }

    #[getter]
    fn reference(&self) -> Option<i32> {
        match self.0 {
            AmbPred::ArenaOk { .. } => None,
            AmbPred::HolSort { ix, .. } => Some(ix.get()),
        }
    }

    #[getter]
    fn classifier(&self) -> Option<i32> {
        match self.0 {
            AmbPred::ArenaOk { .. } => None,
            AmbPred::HolSort { sort, .. } => Some(sort.get()),
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
    fn dense_column(&self, get: impl Fn(&Arena, Ref) -> Option<Ref>) -> PyResult<Vec<Option<i32>>> {
        (1..=self.arena.len())
            .map(|position| {
                let value = i32::try_from(position).map_err(value_error)?;
                Ok(get(&self.arena, reference(value)?).map(Ref::get))
            })
            .collect()
    }

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
        })
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct KernelId(NonZeroU64);

impl KernelId {
    fn fresh() -> Self {
        let value = NEXT_KERNEL_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, checked_add_one)
            .expect("Python kernel identifier space is exhausted");
        Self(NonZeroU64::new(value).expect("kernel identifiers start at one"))
    }
}

const fn checked_add_one(value: u64) -> Option<u64> {
    value.checked_add(1)
}

static NEXT_KERNEL_ID: AtomicU64 = AtomicU64::new(1);

#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolKind"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyKind {
    _owner: KernelId,
    reference: Ref,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKind {
    #[getter]
    const fn reference(&self) -> i32 {
        self.reference.get()
    }
}

#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolTy"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyTy {
    _owner: KernelId,
    reference: Ref,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyTy {
    #[getter]
    const fn reference(&self) -> i32 {
        self.reference.get()
    }
}

#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolTm"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PyTm {
    _owner: KernelId,
    reference: Ref,
}

type PyMatrix = Vec<Vec<i32>>;
type PySequent = (PyMatrix, PyMatrix);

fn python_rows<'a>(rows: impl IntoIterator<Item = &'a [Lit]>) -> PyMatrix {
    rows.into_iter()
        .map(|row| row.iter().map(|literal| literal.get()).collect())
        .collect()
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyTm {
    #[getter]
    const fn reference(&self) -> i32 {
        self.reference.get()
    }
}

/// A checked slot in the syntactic-fact table.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.hol",
    name = "HolSynFact"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
pub struct PySynFact {
    owner: KernelId,
    id: SynFactId,
    fact: SynFact,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySynFact {
    #[getter]
    const fn id(&self) -> i32 {
        self.id.get()
    }

    #[getter]
    fn relation(&self) -> &'static str {
        relation_name(self.fact.rel())
    }

    #[getter]
    fn var(&self) -> Option<i32> {
        self.fact.var().map(Ref::get)
    }

    #[getter]
    fn val(&self) -> Option<i32> {
        self.fact.val().map(Ref::get)
    }

    #[getter]
    const fn input(&self) -> i32 {
        self.fact.input().get()
    }

    #[getter]
    const fn output(&self) -> i32 {
        self.fact.output().get()
    }
}

/// A checked Ethane arena assembled through local LCF operations.
#[pyclass(module = "covalence.logic.hol", name = "HolKernel")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyKernel {
    kernel: Kernel,
    id: KernelId,
}

/// Result of one atomic high-level proposition rewrite.
#[pyclass(
    module = "covalence.logic.hol",
    name = "HolRewriteResult",
    frozen,
    skip_from_py_object
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone, Copy)]
struct PyRewriteResult {
    source: i32,
    target: i32,
    theorem: i32,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRewriteResult {
    /// Proposition consumed by the rewrite.
    #[getter]
    const fn source(&self) -> i32 {
        self.source
    }

    /// Proposition concluded after rewriting.
    #[getter]
    const fn target(&self) -> i32 {
        self.target
    }

    /// Checked theorem concluding `target`.
    #[getter]
    const fn theorem(&self) -> i32 {
        self.theorem
    }
}

impl PyKernel {
    fn checked_fact(&self, fact: &PySynFact) -> PyResult<SynFactId> {
        if self.id != fact.owner {
            return Err(PyValueError::new_err(
                "syntactic fact belongs to a different kernel",
            ));
        }
        let current = self.kernel.syn_fact(fact.id).map_err(value_error)?;
        if current != fact.fact {
            return Err(PyValueError::new_err(
                "syntactic fact handle refers to an overwritten slot",
            ));
        }
        Ok(fact.id)
    }

    fn fact_handle(&self, id: SynFactId) -> PyResult<PySynFact> {
        Ok(PySynFact {
            owner: self.id,
            id,
            fact: self.kernel.syn_fact(id).map_err(value_error)?,
        })
    }
}

/// A reusable portable proof component.
#[pyclass(frozen, module = "covalence.logic.hol", name = "HolProver")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
struct PyProof {
    instance: Mutex<covalence_nucleus::ProofInstance>,
}

struct PythonCas {
    provider: Py<PyAny>,
}

impl AsyncCas for PythonCas {
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<CasBytes>> {
        Box::pin(async move {
            Python::attach(|python| {
                let address = PyO256::wrap(python, address).map_err(python_cas_error)?;
                let returned = self
                    .provider
                    .bind(python)
                    .call_method1("get", (address,))
                    .map_err(python_cas_error)?;
                let bytes = returned.extract::<Bytes>().map_err(python_cas_error)?;
                Ok(Some(CasBytes::copy_from_slice(bytes.as_slice())))
            })
        })
    }
}

impl PyProof {
    fn run(
        &self,
        python: Python<'_>,
        name: covalence_nucleus::ProofName,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        let kernel = match kernel {
            Some(kernel) => kernel,
            None => Py::new(python, PyKernel::new())?,
        };
        let input = kernel.borrow(python).kernel.fork();
        let output = python
            .detach(|| {
                self.instance
                    .lock()
                    .map_err(|_| "proof instance lock is poisoned".to_owned())?
                    .prove(name, input)
                    .map_err(|error| error.to_string())
            })
            .map_err(PyRuntimeError::new_err)?;
        {
            let mut result = kernel.borrow_mut(python);
            result.kernel = output;
            result.id = KernelId::fresh();
        }
        Ok(kernel)
    }
}

fn python_cas_error(error: PyErr) -> AsyncCasError {
    AsyncCasError::provider(std::io::Error::other(error.to_string()))
}

fn python_proof_name(name: Option<&Bound<'_, PyAny>>) -> PyResult<covalence_nucleus::ProofName> {
    let Some(name) = name else {
        return Ok(covalence_nucleus::ProofName::default());
    };
    if let Ok(value) = name.extract::<PyRef<'_, PyO256>>() {
        return Ok(covalence_nucleus::ProofName::Address(PyO256::value(&value)));
    }
    if let Ok(value) = name.extract::<String>() {
        return Ok(covalence_nucleus::ProofName::Text(value));
    }
    if !name.is_instance_of::<PyBool>()
        && let Ok(value) = name.extract::<u64>()
    {
        return Ok(covalence_nucleus::ProofName::Id(value));
    }
    if let Ok(value) = name.extract::<Bytes>() {
        return Ok(covalence_nucleus::ProofName::Bytes(
            CasBytes::copy_from_slice(value.as_slice()),
        ));
    }
    Err(PyTypeError::new_err(
        "proof names must be str, bytes-like, non-negative int, O256, or None",
    ))
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyProof {
    #[new]
    #[pyo3(signature = (source, cas=None))]
    fn new(
        python: Python<'_>,
        source: &Bound<'_, PyAny>,
        cas: Option<Py<PyAny>>,
    ) -> PyResult<Self> {
        let provider = cas.map(|provider| Arc::new(PythonCas { provider }) as Arc<dyn AsyncCas>);
        let instance = if let Ok(address) = source.extract::<PyRef<'_, PyO256>>() {
            let provider = provider.ok_or_else(|| {
                PyValueError::new_err("loading a proof by O256 requires a CAS provider")
            })?;
            let address = PyO256::value(&address);
            python.detach(|| covalence_nucleus::ProofInstance::from_address(address, provider))
        } else {
            let component = source.extract::<Bytes>()?;
            let component = component.as_slice().to_vec();
            python.detach(|| match provider {
                Some(provider) => {
                    covalence_nucleus::ProofInstance::from_bytes_with_cas(&component, provider)
                }
                None => covalence_nucleus::ProofInstance::from_bytes(&component),
            })
        }
        .map_err(|error| PyRuntimeError::new_err(error.to_string()))?;
        Ok(Self {
            instance: Mutex::new(instance),
        })
    }

    /// Requests one prover-local name against an optional input kernel.
    #[pyo3(signature = (name=None, kernel=None))]
    fn prove(
        &self,
        python: Python<'_>,
        name: Option<&Bound<'_, PyAny>>,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        self.run(python, python_proof_name(name)?, kernel)
    }

    #[pyo3(signature = (name, kernel=None))]
    fn prove_addr(
        &self,
        python: Python<'_>,
        name: PyRef<'_, PyO256>,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        self.run(
            python,
            covalence_nucleus::ProofName::Address(PyO256::value(&name)),
            kernel,
        )
    }

    #[pyo3(signature = (name, kernel=None))]
    fn prove_name(
        &self,
        python: Python<'_>,
        name: String,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        self.run(python, covalence_nucleus::ProofName::Text(name), kernel)
    }

    #[pyo3(signature = (name, kernel=None))]
    fn prove_bytes(
        &self,
        python: Python<'_>,
        name: Bytes,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        self.run(
            python,
            covalence_nucleus::ProofName::Bytes(CasBytes::copy_from_slice(name.as_slice())),
            kernel,
        )
    }

    #[pyo3(signature = (ix, kernel=None))]
    fn prove_ix(
        &self,
        python: Python<'_>,
        ix: u64,
        kernel: Option<Py<PyKernel>>,
    ) -> PyResult<Py<PyKernel>> {
        self.run(python, covalence_nucleus::ProofName::Id(ix), kernel)
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyKernel {
    #[new]
    fn new() -> Self {
        Self {
            kernel: Kernel::new(),
            id: KernelId::fresh(),
        }
    }

    #[getter]
    fn arena(&self) -> PyArena {
        PyArena {
            arena: self.kernel.arena().clone(),
        }
    }

    fn addr(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.kernel.addr())
    }

    fn category(&self, reference_value: i32) -> PyResult<&'static str> {
        self.kernel
            .category(reference(reference_value)?)
            .map(sort_name)
            .map_err(value_error)
    }

    fn classifier(&self, reference_value: i32) -> PyResult<i32> {
        self.kernel
            .classifier(reference(reference_value)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn find(&self, reference_value: i32) -> PyResult<i32> {
        self.kernel
            .find(reference(reference_value)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn find_mut(&mut self, reference_value: i32) -> PyResult<i32> {
        self.kernel
            .find_mut(reference(reference_value)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn equivalent(&self, left: i32, right: i32) -> PyResult<bool> {
        self.kernel
            .equivalent(reference(left)?, reference(right)?)
            .map_err(value_error)
    }

    fn kind(&self, reference_value: i32) -> PyResult<PyKind> {
        let reference = reference(reference_value)?;
        if self.kernel.category(reference).map_err(value_error)? != Sort::Kind {
            return Err(PyValueError::new_err("reference is not a kind"));
        }
        Ok(PyKind {
            _owner: self.id,
            reference,
        })
    }

    fn ty(&self, reference_value: i32) -> PyResult<PyTy> {
        let reference = reference(reference_value)?;
        if self.kernel.category(reference).map_err(value_error)? != Sort::Ty {
            return Err(PyValueError::new_err("reference is not a type"));
        }
        Ok(PyTy {
            _owner: self.id,
            reference,
        })
    }

    fn tm(&self, reference_value: i32) -> PyResult<PyTm> {
        let reference = reference(reference_value)?;
        if self.kernel.category(reference).map_err(value_error)? != Sort::Tm {
            return Err(PyValueError::new_err("reference is not a term"));
        }
        Ok(PyTm {
            _owner: self.id,
            reference,
        })
    }

    fn star(&mut self) -> PyResult<i32> {
        self.kernel.star().map(Ref::get).map_err(value_error)
    }

    fn kind_arr(&mut self, domain: i32, codomain: i32) -> PyResult<i32> {
        self.kernel
            .kind_arr(reference(domain)?, reference(codomain)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn bool_ty(&mut self, star: i32) -> PyResult<i32> {
        self.kernel
            .bool_ty(reference(star)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_arr(&mut self, domain: i32, codomain: i32) -> PyResult<i32> {
        self.kernel
            .ty_arr(reference(domain)?, reference(codomain)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_fv(&mut self, name: u64, kind: i32) -> PyResult<i32> {
        self.kernel
            .ty_fv(name, reference(kind)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_app(&mut self, function: i32, argument: i32) -> PyResult<i32> {
        self.kernel
            .ty_app(reference(function)?, reference(argument)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_lam(&mut self, binder: i32, body: i32) -> PyResult<i32> {
        self.kernel
            .ty_lam(reference(binder)?, reference(body)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn model(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        self.kernel
            .model(name, reference(predicate)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_exists(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        self.kernel
            .ty_exists(name, reference(predicate)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn ty_forall(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        self.kernel
            .ty_forall(name, reference(predicate)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn tm_fv(&mut self, name: u64, ty: i32) -> PyResult<i32> {
        self.kernel
            .tm_fv(name, reference(ty)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn app(&mut self, function: i32, argument: i32) -> PyResult<i32> {
        self.kernel
            .app(reference(function)?, reference(argument)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn lam(&mut self, binder: i32, body: i32) -> PyResult<i32> {
        self.kernel
            .lam(reference(binder)?, reference(body)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn bool(&mut self, bool_ty: i32, value: bool) -> PyResult<i32> {
        self.kernel
            .bool(reference(bool_ty)?, value)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn eq(&mut self, bool_ty: i32, left: i32, right: i32) -> PyResult<i32> {
        self.kernel
            .eq(reference(bool_ty)?, reference(left)?, reference(right)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn eps(&mut self, ty: i32, predicate: i32) -> PyResult<i32> {
        self.kernel
            .eps(reference(ty)?, reference(predicate)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn import_literal(&mut self, arena: &PyArena) -> PyResult<i32> {
        ensure_literal_import_can_be_wrapped(&arena.arena)?;
        self.kernel
            .import_literal(arena.arena.clone())
            .map(ImportId::get)
            .map_err(value_error)
    }

    fn import_link(&mut self, link: &PyLink) -> PyResult<i32> {
        self.kernel
            .import_link(link.0)
            .map(ImportId::get)
            .map_err(value_error)
    }

    fn add_context(&mut self, proposition: i32) -> PyResult<()> {
        self.kernel
            .add_context(reference(proposition)?)
            .map_err(value_error)
    }

    fn add_axiom(&mut self, name: &str) -> PyResult<()> {
        self.kernel.add_axiom(name).map_err(value_error)
    }

    /// Encodes a Boolean term reference as a positive or negated i32 literal.
    #[pyo3(signature = (reference_value, negated=false))]
    #[allow(
        clippy::unused_self,
        reason = "the Python API scopes literals by kernel flavor"
    )]
    fn lit(&self, reference_value: i32, negated: bool) -> PyResult<i32> {
        let reference = reference(reference_value)?;
        let magnitude = reference.get();
        if magnitude == i32::MAX {
            return Err(PyValueError::new_err(
                "literal magnitude must be below i32::MAX",
            ));
        }
        // Rule application performs the authoritative resident Boolean check.
        let positive = Lit::positive(magnitude);
        Ok(if negated {
            positive.negated()
        } else {
            positive
        }
        .get())
    }

    fn logical_not(&mut self, operand: i32) -> PyResult<i32> {
        self.kernel
            .op1(Op1::Not, reference(operand)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn logical_and(&mut self, left: i32, right: i32) -> PyResult<i32> {
        self.kernel
            .op2(Op2::And, reference(left)?, reference(right)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn logical_or(&mut self, left: i32, right: i32) -> PyResult<i32> {
        self.kernel
            .op2(Op2::Or, reference(left)?, reference(right)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn logical_imp(&mut self, left: i32, right: i32) -> PyResult<i32> {
        self.kernel
            .op2(Op2::Imp, reference(left)?, reference(right)?)
            .map(Ref::get)
            .map_err(value_error)
    }

    fn theorem(&self, id: i32) -> PyResult<PySequent> {
        let id = theorem_id(id)?;
        let theorem = self
            .kernel
            .thm()
            .get(id)
            .ok_or_else(|| PyValueError::new_err(format!("theorem {} is absent", id.get())))?;
        Ok((
            python_rows(theorem.lhs.rows()),
            python_rows(theorem.rhs.rows()),
        ))
    }

    fn copy_refutation_to_syllogisms(
        &mut self,
        refutation: PyRef<'_, crate::lrat::PyRefutation>,
    ) -> PyResult<i32> {
        self.kernel
            .syl_mut()
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn copy_refutation_to_theorems(
        &mut self,
        refutation: PyRef<'_, crate::lrat::PyRefutation>,
    ) -> PyResult<i32> {
        self.kernel
            .thm_mut()
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn identity(&mut self, proposition: i32) -> PyResult<i32> {
        self.kernel
            .identity(literal(proposition)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn weaken(&mut self, theorem: i32, premises: Vec<i32>, conclusions: Vec<i32>) -> PyResult<()> {
        let id = theorem_id(theorem)?;
        let premises = literals(premises)?;
        let conclusions = literals(conclusions)?;
        self.kernel
            .weaken(id, &premises, &conclusions)
            .map_err(value_error)?;
        Ok(())
    }

    fn weaken_matrix(
        &mut self,
        theorem: i32,
        premises: Vec<Vec<i32>>,
        conclusions: Vec<Vec<i32>>,
    ) -> PyResult<()> {
        let id = theorem_id(theorem)?;
        let premises = matrix(premises)?;
        let conclusions = matrix(conclusions)?;
        self.kernel
            .weaken_matrix(id, &premises, &conclusions)
            .map_err(value_error)?;
        Ok(())
    }

    fn move_cnf_right(&mut self, theorem: i32, row: i32) -> PyResult<()> {
        let id = theorem_id(theorem)?;
        let row = cnf_id(row)?;
        self.kernel.move_cnf_right(id, row).map_err(value_error)?;
        Ok(())
    }

    fn move_dnf_left(&mut self, theorem: i32, row: i32) -> PyResult<()> {
        let id = theorem_id(theorem)?;
        let row = dnf_id(row)?;
        self.kernel.move_dnf_left(id, row).map_err(value_error)?;
        Ok(())
    }

    fn normalize_cnf(&mut self, theorem: i32, row: i32) -> PyResult<()> {
        self.kernel
            .normalize_cnf(theorem_id(theorem)?, cnf_id(row)?)
            .map_err(value_error)
    }

    fn normalize_dnf(&mut self, theorem: i32, row: i32) -> PyResult<()> {
        self.kernel
            .normalize_dnf(theorem_id(theorem)?, dnf_id(row)?)
            .map_err(value_error)
    }

    fn cut(&mut self, left: i32, right: i32, proposition: i32) -> PyResult<i32> {
        self.kernel
            .cut(theorem_id(left)?, theorem_id(right)?, literal(proposition)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn resolve(&mut self, left: i32, right: i32, pivot: i32) -> PyResult<i32> {
        self.kernel
            .resolve(theorem_id(left)?, theorem_id(right)?, literal(pivot)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn false_left(&mut self, falsehood: i32) -> PyResult<i32> {
        self.kernel
            .false_left(literal(falsehood)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn true_right(&mut self, truth: i32) -> PyResult<i32> {
        self.kernel
            .true_right(literal(truth)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn not_left(&mut self, theorem: i32, proposition: i32) -> PyResult<()> {
        self.kernel
            .not_left(theorem_id(theorem)?, literal(proposition)?)
            .map_err(value_error)
    }

    fn not_right(&mut self, theorem: i32, proposition: i32) -> PyResult<()> {
        self.kernel
            .not_right(theorem_id(theorem)?, literal(proposition)?)
            .map_err(value_error)
    }

    fn and_left(&mut self, theorem: i32, conjunction: i32) -> PyResult<i32> {
        self.kernel
            .and_left(theorem_id(theorem)?, literal(conjunction)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn and_right(&mut self, left: i32, right: i32, conjunction: i32) -> PyResult<i32> {
        self.kernel
            .and_right(theorem_id(left)?, theorem_id(right)?, literal(conjunction)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn or_left(&mut self, left: i32, right: i32, disjunction: i32) -> PyResult<i32> {
        self.kernel
            .or_left(theorem_id(left)?, theorem_id(right)?, literal(disjunction)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn or_right(&mut self, theorem: i32, disjunction: i32) -> PyResult<i32> {
        self.kernel
            .or_right(theorem_id(theorem)?, literal(disjunction)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn imp_left(&mut self, left: i32, right: i32, implication: i32) -> PyResult<i32> {
        self.kernel
            .imp_left(theorem_id(left)?, theorem_id(right)?, literal(implication)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn imp_right(&mut self, theorem: i32, implication: i32) -> PyResult<i32> {
        self.kernel
            .imp_right(theorem_id(theorem)?, literal(implication)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    #[pyo3(signature = (theorem, formula, branch=None))]
    fn expand_conclusion(
        &mut self,
        theorem: i32,
        formula: i32,
        branch: Option<bool>,
    ) -> PyResult<i32> {
        self.kernel
            .expand_conclusion(theorem_id(theorem)?, literal(formula)?, branch)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn flatten_conclusion(&mut self, theorem: i32, formula: i32) -> PyResult<i32> {
        self.kernel
            .flatten_conclusion(theorem_id(theorem)?, literal(formula)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn flatten_premise(&mut self, theorem: i32, formula: i32) -> PyResult<i32> {
        self.kernel
            .flatten_premise(theorem_id(theorem)?, literal(formula)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn fold_premise(&mut self, theorem: i32, formula: i32) -> PyResult<i32> {
        self.kernel
            .fold_premise(theorem_id(theorem)?, literal(formula)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn fold_conclusion(&mut self, theorem: i32, formula: i32) -> PyResult<i32> {
        self.kernel
            .fold_conclusion(theorem_id(theorem)?, literal(formula)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn copy_theorem(&mut self, theorem: i32) -> PyResult<i32> {
        self.kernel
            .copy_theorem(theorem_id(theorem)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn refl(&mut self, bool_ty: i32, term: i32) -> PyResult<(i32, i32)> {
        self.kernel
            .refl(reference(bool_ty)?, reference(term)?)
            .map(|result| (result.equality.get(), result.theorem.get()))
            .map_err(value_error)
    }

    fn ap_thm(&mut self, theorem: i32, argument: i32) -> PyResult<(i32, i32, i32, i32)> {
        self.kernel
            .ap_thm(theorem_id(theorem)?, reference(argument)?)
            .map(|result| {
                (
                    result.left.get(),
                    result.right.get(),
                    result.equality.get(),
                    result.theorem.get(),
                )
            })
            .map_err(value_error)
    }

    fn ap_term(&mut self, theorem: i32, function: i32) -> PyResult<(i32, i32, i32, i32)> {
        self.kernel
            .ap_term(theorem_id(theorem)?, reference(function)?)
            .map(|result| {
                (
                    result.left.get(),
                    result.right.get(),
                    result.equality.get(),
                    result.theorem.get(),
                )
            })
            .map_err(value_error)
    }

    fn eq_mp(&mut self, equality: i32, premise: i32) -> PyResult<i32> {
        self.kernel
            .eq_mp(theorem_id(equality)?, theorem_id(premise)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    #[pyo3(signature = (bool_ty, equality, premise, direction="forward"))]
    fn rewrite_proposition(
        &mut self,
        bool_ty: i32,
        equality: i32,
        premise: i32,
        direction: &str,
    ) -> PyResult<PyRewriteResult> {
        let direction = match direction {
            "forward" => covalence_nucleus::tactics::RewriteDirection::Forward,
            "backward" => covalence_nucleus::tactics::RewriteDirection::Backward,
            _ => {
                return Err(PyValueError::new_err(
                    "direction must be forward or backward",
                ));
            }
        };
        covalence_nucleus::tactics::rewrite_proposition(
            &mut self.kernel,
            reference(bool_ty)?,
            theorem_id(equality)?,
            theorem_id(premise)?,
            direction,
        )
        .map(|result| PyRewriteResult {
            source: result.source().get(),
            target: result.target().get(),
            theorem: result.theorem().get(),
        })
        .map_err(value_error)
    }

    fn forall_intro(&mut self, theorem: i32, binder: i32) -> PyResult<(i32, i32)> {
        self.kernel
            .forall_intro(theorem_id(theorem)?, reference(binder)?)
            .map(|result| (result.universal.get(), result.theorem.get()))
            .map_err(value_error)
    }

    fn forall_intro_at(&mut self, theorem: i32, binder: i32, universal: i32) -> PyResult<i32> {
        self.kernel
            .forall_intro_at(
                theorem_id(theorem)?,
                reference(binder)?,
                reference(universal)?,
            )
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn choice_intro(&mut self, theorem: i32) -> PyResult<(i32, i32, i32)> {
        self.kernel
            .choice_intro(theorem_id(theorem)?)
            .map(|result| {
                (
                    result.witness.get(),
                    result.proposition.get(),
                    result.theorem.get(),
                )
            })
            .map_err(value_error)
    }

    fn choice_intro_at(&mut self, theorem: i32, target: i32) -> PyResult<i32> {
        self.kernel
            .choice_intro_at(theorem_id(theorem)?, reference(target)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn convert_theorem(&mut self, theorem: i32, source: i32, target: i32) -> PyResult<()> {
        self.kernel
            .convert_theorem(theorem_id(theorem)?, reference(source)?, reference(target)?)
            .map_err(value_error)
    }

    fn convert_conclusions(&mut self, theorem: i32, source: i32, target: i32) -> PyResult<()> {
        self.kernel
            .convert_conclusions(theorem_id(theorem)?, reference(source)?, reference(target)?)
            .map_err(value_error)
    }

    fn contract_theorem(&mut self, theorem: i32) -> PyResult<()> {
        self.kernel
            .contract_theorem(theorem_id(theorem)?)
            .map_err(value_error)
    }

    fn eqt_elim(&mut self, theorem: i32) -> PyResult<i32> {
        self.kernel
            .eqt_elim(theorem_id(theorem)?)
            .map(ThmId::get)
            .map_err(value_error)
    }

    fn remove_theorem(&mut self, theorem: i32) -> PyResult<bool> {
        Ok(self.kernel.remove_theorem(theorem_id(theorem)?))
    }

    fn syn_fact(&self, id: i32) -> PyResult<PySynFact> {
        self.fact_handle(fact_id(id)?)
    }

    fn syn_fact_len(&self) -> usize {
        self.kernel.syn_fact_len()
    }

    fn remove_syn_fact(&mut self, fact: &PySynFact) -> PyResult<bool> {
        let id = self.checked_fact(fact)?;
        Ok(self.kernel.remove_syn_fact(id))
    }

    fn truncate_syn_facts(&mut self, len: usize) {
        self.kernel.truncate_syn_facts(len);
    }

    #[pyo3(signature = (relation, input, target=None))]
    fn syn_refl(&mut self, relation: &str, input: i32, target: Option<i32>) -> PyResult<PySynFact> {
        let id = self
            .kernel
            .syn_refl(
                fact_target(target)?,
                parse_relation(relation)?,
                reference(input)?,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (source, relation, target=None))]
    fn syn_refine(
        &mut self,
        source: &PySynFact,
        relation: &str,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let source = self.checked_fact(source)?;
        let id = self
            .kernel
            .syn_refine(fact_target(target)?, source, parse_relation(relation)?)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (source, target=None))]
    fn syn_symm(&mut self, source: &PySynFact, target: Option<i32>) -> PyResult<PySynFact> {
        let source = self.checked_fact(source)?;
        let id = self
            .kernel
            .syn_symm(fact_target(target)?, source)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (left, right, target=None))]
    fn syn_trans(
        &mut self,
        left: &PySynFact,
        right: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let left = self.checked_fact(left)?;
        let right = self.checked_fact(right)?;
        let id = self
            .kernel
            .syn_trans(fact_target(target)?, left, right)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (var, val, target=None))]
    fn syn_sub_var(&mut self, var: i32, val: i32, target: Option<i32>) -> PyResult<PySynFact> {
        let id = self
            .kernel
            .syn_sub_var(fact_target(target)?, reference(var)?, reference(val)?)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (var, val, input, target=None))]
    fn syn_sub_leaf(
        &mut self,
        var: i32,
        val: i32,
        input: i32,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let id = self
            .kernel
            .syn_sub_leaf(
                fact_target(target)?,
                reference(var)?,
                reference(val)?,
                reference(input)?,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (var, val, input, output, variable_equality, body_equality, target=None))]
    #[allow(clippy::too_many_arguments)]
    fn syn_sub_identity(
        &mut self,
        var: i32,
        val: i32,
        input: i32,
        output: i32,
        variable_equality: &PySynFact,
        body_equality: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let variable_equality = self.checked_fact(variable_equality)?;
        let body_equality = self.checked_fact(body_equality)?;
        let id = self
            .kernel
            .syn_sub_identity(
                fact_target(target)?,
                reference(var)?,
                reference(val)?,
                reference(input)?,
                reference(output)?,
                variable_equality,
                body_equality,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (relation, input, output, children, var=None, val=None, target=None))]
    #[allow(clippy::too_many_arguments)]
    fn syn_congr(
        &mut self,
        relation: &str,
        input: i32,
        output: i32,
        children: Vec<PyRef<'_, PySynFact>>,
        var: Option<i32>,
        val: Option<i32>,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let evidence = children
            .iter()
            .map(|fact| self.checked_fact(fact))
            .collect::<PyResult<Vec<_>>>()?;
        let id = self
            .kernel
            .syn_congr(
                fact_target(target)?,
                parse_relation(relation)?,
                var.map(reference).transpose()?,
                val.map(reference).transpose()?,
                reference(input)?,
                reference(output)?,
                &evidence,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (relation, input, output, binder, body, var=None, val=None, target=None))]
    #[allow(clippy::too_many_arguments)]
    fn syn_binder_congr(
        &mut self,
        relation: &str,
        input: i32,
        output: i32,
        binder: &PySynFact,
        body: &PySynFact,
        var: Option<i32>,
        val: Option<i32>,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let binder = self.checked_fact(binder)?;
        let body = self.checked_fact(body)?;
        let id = self
            .kernel
            .syn_binder_congr(
                fact_target(target)?,
                parse_relation(relation)?,
                var.map(reference).transpose()?,
                val.map(reference).transpose()?,
                reference(input)?,
                reference(output)?,
                binder,
                body,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (relation, input, output, binder, body, var=None, val=None, target=None))]
    #[allow(clippy::too_many_arguments)]
    fn syn_implicit_binder_congr(
        &mut self,
        relation: &str,
        input: i32,
        output: i32,
        binder: i32,
        body: &PySynFact,
        var: Option<i32>,
        val: Option<i32>,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let body = self.checked_fact(body)?;
        let id = self
            .kernel
            .syn_implicit_binder_congr(
                fact_target(target)?,
                parse_relation(relation)?,
                var.map(reference).transpose()?,
                val.map(reference).transpose()?,
                reference(input)?,
                reference(output)?,
                reference(binder)?,
                body,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (input, output, binder_classifier, body_substitution, target=None))]
    fn syn_alpha_binder(
        &mut self,
        input: i32,
        output: i32,
        binder_classifier: &PySynFact,
        body_substitution: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let binder_classifier = self.checked_fact(binder_classifier)?;
        let body_substitution = self.checked_fact(body_substitution)?;
        let id = self
            .kernel
            .syn_alpha_binder(
                fact_target(target)?,
                reference(input)?,
                reference(output)?,
                binder_classifier,
                body_substitution,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (input, output, input_binder, output_binder, body_substitution, target=None))]
    #[allow(clippy::too_many_arguments)]
    fn syn_alpha_implicit_binder(
        &mut self,
        input: i32,
        output: i32,
        input_binder: i32,
        output_binder: i32,
        body_substitution: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let body_substitution = self.checked_fact(body_substitution)?;
        let id = self
            .kernel
            .syn_alpha_implicit_binder(
                fact_target(target)?,
                reference(input)?,
                reference(output)?,
                reference(input_binder)?,
                reference(output_binder)?,
                body_substitution,
            )
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (source, substitution, target=None))]
    fn tm_beta(
        &mut self,
        source: i32,
        substitution: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let substitution = self.checked_fact(substitution)?;
        let id = self
            .kernel
            .tm_beta_fact(fact_target(target)?, reference(source)?, substitution)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (source, substitution, target=None))]
    fn ty_beta(
        &mut self,
        source: i32,
        substitution: &PySynFact,
        target: Option<i32>,
    ) -> PyResult<PySynFact> {
        let substitution = self.checked_fact(substitution)?;
        let id = self
            .kernel
            .ty_beta_fact(fact_target(target)?, reference(source)?, substitution)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    #[pyo3(signature = (source, target=None))]
    fn tm_eta(&mut self, source: i32, target: Option<i32>) -> PyResult<PySynFact> {
        let id = self
            .kernel
            .tm_eta_fact(fact_target(target)?, reference(source)?)
            .map_err(value_error)?;
        self.fact_handle(id)
    }

    fn union_syn_fact(&mut self, fact: &PySynFact) -> PyResult<()> {
        let fact = self.checked_fact(fact)?;
        self.kernel.union_syn_fact(fact).map_err(value_error)
    }

    fn __len__(&self) -> usize {
        self.kernel.arena().len()
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyLink>()?;
    module.add_class::<PyDefinition>()?;
    module.add_class::<PyAmbPred>()?;
    module.add_class::<PyArena>()?;
    module.add_class::<PyKind>()?;
    module.add_class::<PyTy>()?;
    module.add_class::<PyTm>()?;
    module.add_class::<PySynFact>()?;
    module.add_class::<PyKernel>()?;
    module.add_class::<PyRewriteResult>()?;
    module.add_class::<PyProof>()?;
    Ok(())
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

    fn addr(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.arena.addr())
    }

    fn definition(&self, reference_value: i32) -> PyResult<Option<PyDefinition>> {
        if reference_value == 0 {
            return Err(PyValueError::new_err("references are one-based"));
        }
        let Some(reference) = Ref::new(reference_value) else {
            return Ok(None);
        };
        Ok(self.definition_at(reference))
    }

    #[getter]
    fn definitions(&self) -> PyResult<Vec<PyDefinition>> {
        (1..=self.arena.len())
            .map(|position| {
                let value = i32::try_from(position).map_err(value_error)?;
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
    fn context(&self) -> Vec<i32> {
        self.arena.context().map(Ref::get).collect()
    }

    /// Semantic-equality representatives, aligned with `definitions`.
    #[getter]
    fn eq(&self) -> PyResult<Vec<Option<i32>>> {
        self.dense_column(Arena::eq)
    }

    /// Syntactic-equality representatives, aligned with `definitions`.
    #[getter]
    fn syn_eq(&self) -> PyResult<Vec<Option<i32>>> {
        self.dense_column(Arena::syn_eq)
    }

    /// Conversion-equality representatives, aligned with `definitions`.
    #[getter]
    fn conv(&self) -> PyResult<Vec<Option<i32>>> {
        self.dense_column(Arena::conv)
    }

    #[getter]
    fn amb_pred(&self) -> Vec<PyAmbPred> {
        self.arena
            .ambient_predicates()
            .iter()
            .copied()
            .map(PyAmbPred)
            .collect()
    }

    #[getter]
    fn amb_ax(&self) -> Vec<String> {
        self.arena.ambient_axioms().map(str::to_owned).collect()
    }

    #[getter]
    fn amb_ctx(&self) -> Vec<Vec<i32>> {
        self.arena
            .ambient_context()
            .rows()
            .map(|row| row.iter().map(|literal| literal.get()).collect())
            .collect()
    }

    #[getter]
    fn amb_thm(&self) -> Vec<PySequent> {
        classical_rows(self.arena.ambient_theorems())
    }

    #[getter]
    fn pred_syl(&self) -> Vec<PySequent> {
        classical_rows(self.arena.syllogisms())
    }

    #[getter]
    fn hol_thm(&self) -> Vec<PySequent> {
        classical_rows(self.arena.theorems())
    }

    fn add_null_import(&mut self) -> PyResult<i32> {
        imported(self.arena.push_import(Import::Null))
    }

    fn add_literal_import(&mut self, arena: &Self) -> PyResult<i32> {
        ensure_literal_import_can_be_wrapped(&arena.arena)?;
        imported(
            self.arena
                .push_import(Import::Literal(Box::new(arena.arena.clone()))),
        )
    }

    fn add_link_import(&mut self, link: &PyLink) -> PyResult<i32> {
        imported(self.arena.push_import(Import::Link(link.0)))
    }

    fn add_axiom(&mut self, name: &str) {
        self.arena.insert_axiom(name);
    }

    fn add_context(&mut self, reference_value: i32) -> PyResult<()> {
        self.arena.insert_context(reference(reference_value)?);
        Ok(())
    }

    fn amb_ctx_arena_ok(&mut self, source_value: i32) -> PyResult<()> {
        push_amb_ctx(
            &mut self.arena,
            AmbPred::ArenaOk {
                src: source(source_value)?,
            },
        )
    }

    fn amb_thm_arena_ok(&mut self, source_value: i32) -> PyResult<()> {
        push_amb_thm(
            &mut self.arena,
            AmbPred::ArenaOk {
                src: source(source_value)?,
            },
        )
    }

    fn amb_ctx_hol_sort(&mut self, source_value: i32, ix: i32, sort: i32) -> PyResult<()> {
        push_amb_ctx(
            &mut self.arena,
            AmbPred::HolSort {
                src: source(source_value)?,
                ix: reference(ix)?,
                sort: reference(sort)?,
            },
        )
    }

    fn amb_thm_hol_sort(&mut self, source_value: i32, ix: i32, sort: i32) -> PyResult<()> {
        push_amb_thm(
            &mut self.arena,
            AmbPred::HolSort {
                src: source(source_value)?,
                ix: reference(ix)?,
                sort: reference(sort)?,
            },
        )
    }

    fn kind_star(&mut self) -> PyResult<i32> {
        allocated(self.arena.push_kind_star())
    }

    fn kind_arr(&mut self, domain: i32, codomain: i32) -> PyResult<i32> {
        let domain = reference(domain)?;
        let codomain = reference(codomain)?;
        allocated(self.arena.push_kind_arr(domain, codomain))
    }

    fn bool_ty(&mut self) -> PyResult<i32> {
        allocated(self.arena.push_bool_ty())
    }

    fn ty_arr(&mut self, domain: i32, codomain: i32) -> PyResult<i32> {
        let domain = reference(domain)?;
        let codomain = reference(codomain)?;
        allocated(self.arena.push_ty_arr(domain, codomain))
    }

    fn ty_app(&mut self, function: i32, argument: i32) -> PyResult<i32> {
        let function = reference(function)?;
        let argument = reference(argument)?;
        allocated(self.arena.push_ty_app(function, argument))
    }

    fn ty_lam(&mut self, binder: i32, body: i32) -> PyResult<i32> {
        let binder = reference(binder)?;
        let body = reference(body)?;
        allocated(self.arena.push_ty_lam(binder, body))
    }

    fn ty_fv(&mut self, name: u64, kind: i32) -> PyResult<i32> {
        let kind = reference(kind)?;
        allocated(self.arena.push_ty_fv(name, kind))
    }

    fn ty_exists(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        let predicate = reference(predicate)?;
        allocated(self.arena.push_ty_exists(name, predicate))
    }

    fn ty_forall(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        let predicate = reference(predicate)?;
        allocated(self.arena.push_ty_forall(name, predicate))
    }

    fn model(&mut self, name: u64, predicate: i32) -> PyResult<i32> {
        let predicate = reference(predicate)?;
        allocated(self.arena.push_model(name, predicate))
    }

    fn tm_fv(&mut self, name: u64, ty: i32) -> PyResult<i32> {
        let ty = reference(ty)?;
        allocated(self.arena.push_tm_fv(name, ty))
    }

    fn app(&mut self, function: i32, argument: i32) -> PyResult<i32> {
        let function = reference(function)?;
        let argument = reference(argument)?;
        allocated(self.arena.push_app(function, argument))
    }

    fn lam(&mut self, binder: i32, body: i32) -> PyResult<i32> {
        let binder = reference(binder)?;
        let body = reference(body)?;
        allocated(self.arena.push_lam(binder, body))
    }

    fn bool(&mut self, value: bool) -> PyResult<i32> {
        allocated(self.arena.push_bool(value))
    }

    fn tm_eq(&mut self, left: i32, right: i32) -> PyResult<i32> {
        let left = reference(left)?;
        let right = reference(right)?;
        allocated(self.arena.push_tm_eq(left, right))
    }

    fn eps(&mut self, ty: i32, predicate: i32) -> PyResult<i32> {
        let ty = reference(ty)?;
        let predicate = reference(predicate)?;
        allocated(self.arena.push_eps(ty, predicate))
    }

    fn tm_ref(&mut self, source_value: i32, foreign: i32) -> PyResult<i32> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_tm_ref(source, foreign))
    }

    fn ty_ref(&mut self, source_value: i32, foreign: i32) -> PyResult<i32> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_ty_ref(source, foreign))
    }

    fn kind_ref(&mut self, source_value: i32, foreign: i32) -> PyResult<i32> {
        let source = source(source_value)?;
        let foreign = reference(foreign)?;
        allocated(self.arena.push_kind_ref(source, foreign))
    }

    fn __len__(&self) -> usize {
        self.arena.len()
    }
}
