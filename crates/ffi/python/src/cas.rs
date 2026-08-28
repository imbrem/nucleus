//! Whole-object and range CAS facts, and indexed userspace storage, for Python.

#![allow(clippy::needless_pass_by_value)]

use std::hash::{DefaultHasher, Hash, Hasher};

use covalence_data_cas::IndexCas;
use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    basic::CompareOp,
    exceptions::PyLookupError,
    types::{PyBytes, PyType},
};
use covalence_logic_cas::{
    Blake3Cv, BlobSpan, Bytes as CasBytes, CasAssertion, CasFact, CasRangeAssertion, CasRangeFact,
    RangeProof,
};

use crate::hash::PyO256;

create_exception!(
    covalence,
    CasCheckError,
    PyValueError,
    "A CAS assertion or proof failed validation."
);
create_exception!(
    covalence,
    CasDigestMismatchError,
    CasCheckError,
    "A whole-object CAS assertion carried the wrong content hash."
);
create_exception!(
    covalence,
    CasRangeError,
    CasCheckError,
    "A CAS range was not derivable from the facts at hand."
);
create_exception!(
    covalence,
    CasProofError,
    CasCheckError,
    "A CAS range proof was unusable."
);
create_exception!(
    covalence,
    CasLookupError,
    PyLookupError,
    "A CAS lookup failed."
);
create_exception!(
    covalence,
    CasNotFoundError,
    CasLookupError,
    "A CAS does not contain the requested address."
);
create_exception!(
    covalence,
    CasAddressMismatchError,
    CasLookupError,
    "A CAS returned a checked fact for another address."
);

fn check_error(error: covalence_logic_cas::CasCheckError) -> PyErr {
    CasDigestMismatchError::new_err(error.to_string())
}

fn range_error(error: &impl std::fmt::Display) -> PyErr {
    CasRangeError::new_err(error.to_string())
}

/// Maps a proof failure, keeping a wrong root a digest mismatch rather than
/// flattening it into the malformed-proof case.
fn proof_error(error: &covalence_logic_cas::RangeProofError) -> PyErr {
    match error {
        covalence_logic_cas::RangeProofError::Root { source } => check_error(*source),
        other => CasProofError::new_err(other.to_string()),
    }
}

/// Builds the one range shape Python sees.
///
/// Rust decides open-versus-closed by type; Python carries it as an `end` of
/// `None`, which is why the binding exposes `BlobSpan` rather than the four
/// static shapes.
fn span(start: u64, end: Option<u64>) -> PyResult<BlobSpan> {
    BlobSpan::new(start, end).ok_or_else(|| {
        CasRangeError::new_err(format!(
            "range start {start} is after range end {}",
            end.unwrap_or_default()
        ))
    })
}

fn hash_value(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// An ordinary, unchecked claim about one complete content-addressed blob.
#[pyclass(frozen, module = "covalence.cas", name = "CasAssertion")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCasAssertion(CasAssertion);

impl PyCasAssertion {
    fn wrap(assertion: CasAssertion) -> Self {
        Self(assertion)
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCasAssertion {
    /// Constructs an unchecked assertion without hashing its blob.
    #[new]
    fn new(hash: PyRef<'_, PyO256>, blob: Bytes) -> Self {
        Self(CasAssertion::new(
            PyO256::value(&hash),
            ..,
            CasBytes::copy_from_slice(blob.as_slice()),
        ))
    }

    /// Claimed content address.
    #[getter]
    fn hash(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.hash)
    }

    /// Complete claimed bytes.
    #[getter]
    fn blob<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, &self.0.bytes)
    }

    /// Checks every byte and introduces a fact on success.
    ///
    /// # Errors
    ///
    /// Raises `CasDigestMismatchError` when the claimed address is wrong.
    fn check(&self, python: Python<'_>) -> PyResult<Py<PyCasFact>> {
        let assertion = self.0.clone();
        let fact = python.detach(|| assertion.check()).map_err(check_error)?;
        PyCasFact::wrap(python, fact)
    }

    fn __repr__(&self) -> String {
        format!(
            "CasAssertion(hash=O256.from_hex('{}'), blob_len={})",
            self.0.hash,
            self.0.bytes.len()
        )
    }

    fn __richcmp__(&self, other: &Self, op: CompareOp) -> bool {
        op.matches(self.0.cmp(&other.0))
    }

    fn __hash__(&self) -> u64 {
        hash_value(&self.0)
    }
}

/// An opaque checked fact about a complete content-addressed blob.
///
/// `CasFact` is separate from `CasAssertion`: callers can explicitly forget
/// checkedness through [`Self::assertion`], but unchecked data is never a fact
/// merely by inheritance.
#[pyclass(frozen, module = "covalence.cas", name = "CasFact")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCasFact(CasFact);

impl PyCasFact {
    fn wrap(python: Python<'_>, fact: CasFact) -> PyResult<Py<Self>> {
        Py::new(python, Self(fact))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCasFact {
    /// Checks a specific address and complete blob.
    ///
    /// # Errors
    ///
    /// Raises `CasDigestMismatchError` when `hash` is not the blob's address.
    #[new]
    fn new(python: Python<'_>, hash: PyRef<'_, PyO256>, blob: Bytes) -> PyResult<Py<Self>> {
        let hash = PyO256::value(&hash);
        let blob = CasBytes::copy_from_slice(blob.as_slice());
        let fact = python
            .detach(|| CasFact::new(hash, blob))
            .map_err(check_error)?;
        Self::wrap(python, fact)
    }

    /// Checks an existing assertion.
    ///
    /// # Errors
    ///
    /// Raises `CasDigestMismatchError` when the assertion is false.
    #[staticmethod]
    fn from_assertion(
        python: Python<'_>,
        assertion: PyRef<'_, PyCasAssertion>,
    ) -> PyResult<Py<Self>> {
        let assertion = assertion.0.clone();
        let fact = python.detach(|| assertion.check()).map_err(check_error)?;
        Self::wrap(python, fact)
    }

    /// Hashes complete bytes and returns the resulting fact.
    #[staticmethod]
    fn from_bytes(python: Python<'_>, blob: Bytes) -> PyResult<Py<Self>> {
        let blob = CasBytes::copy_from_slice(blob.as_slice());
        let fact = python.detach(|| CasFact::from_bytes(blob));
        Self::wrap(python, fact)
    }

    /// Checked content address.
    #[getter]
    fn hash(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.hash())
    }

    /// Complete checked bytes.
    #[getter]
    fn blob<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, self.0.bytes())
    }

    /// Returns the underlying assertion, forgetting checkedness.
    #[getter]
    fn assertion(&self) -> PyCasAssertion {
        PyCasAssertion::wrap(CasAssertion::from(&self.0))
    }

    /// Derives a checked range fact from this whole-blob fact.
    ///
    /// Offsets are absolute. An `end` of `None` runs to the end of the blob,
    /// so the result also knows the blob's length.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when the range is not within this blob.
    #[pyo3(signature = (start, end = None))]
    fn range(
        &self,
        python: Python<'_>,
        start: u64,
        end: Option<u64>,
    ) -> PyResult<Py<PyCasRangeFact>> {
        let fact = self
            .0
            .slice(span(start, end)?)
            .map_err(|error| range_error(&error))?;
        PyCasRangeFact::wrap(python, fact)
    }

    fn __repr__(&self) -> String {
        format!(
            "CasFact(hash=O256.from_hex('{}'), blob_len={})",
            self.0.hash(),
            self.0.bytes().len()
        )
    }

    fn __richcmp__(&self, other: &Self, op: CompareOp) -> bool {
        op.matches(self.0.cmp(&other.0))
    }

    fn __hash__(&self) -> u64 {
        hash_value(&self.0)
    }
}

/// An ordinary, unchecked claim about one byte range of a CAS blob.
///
/// `end` is `None` when the range runs to the end of the blob, which is the
/// stronger claim: it also says how long the blob is. Rust decides that by
/// type, with a separate range type per shape; Python carries the one erased
/// shape, so the distinction lives in `end` rather than in the class.
#[pyclass(frozen, module = "covalence.cas", name = "CasRangeAssertion")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCasRangeAssertion(CasRangeAssertion<BlobSpan>);

impl PyCasRangeAssertion {
    fn wrap(assertion: CasRangeAssertion<BlobSpan>) -> Self {
        Self(assertion)
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCasRangeAssertion {
    /// Records a claim without checking it.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when `end` precedes `start`.
    #[new]
    #[pyo3(signature = (hash, start, end, bytes))]
    fn new(hash: PyRef<'_, PyO256>, start: u64, end: Option<u64>, bytes: Bytes) -> PyResult<Self> {
        Ok(Self(CasRangeAssertion::new(
            PyO256::value(&hash),
            span(start, end)?,
            CasBytes::copy_from_slice(bytes.as_slice()),
        )))
    }

    /// Claimed content address of the complete blob.
    #[getter]
    fn hash(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.hash)
    }

    /// First byte offset the range covers.
    #[getter]
    const fn start(&self) -> u64 {
        self.0.range.start()
    }

    /// One past the last byte, or `None` for the end of the blob.
    #[getter]
    const fn end(&self) -> Option<u64> {
        self.0.range.end()
    }

    /// Claimed bytes at that range.
    #[getter]
    fn bytes<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, &self.0.bytes)
    }

    /// Checks this claim against a range proof.
    ///
    /// There is deliberately no argument-free conversion: a range assertion
    /// becomes a fact only by a proof, or by deriving it from a fact that
    /// already covers those bytes.
    ///
    /// # Errors
    ///
    /// Raises `CasProofError` when the proof does not describe a tree above
    /// the range, or `CasDigestMismatchError` when it reaches another address.
    fn check(
        &self,
        python: Python<'_>,
        proof: PyRef<'_, PyRangeProof>,
    ) -> PyResult<Py<PyCasRangeFact>> {
        let assertion = self.0.clone();
        let proof = proof.0.clone();
        let fact = python
            .detach(|| proof.check(assertion.hash, assertion.range, assertion.bytes))
            .map_err(|error| proof_error(&error))?;
        PyCasRangeFact::wrap(python, fact)
    }

    fn __repr__(&self) -> String {
        format!(
            "CasRangeAssertion(hash=O256.from_hex('{}'), range={}, bytes_len={})",
            self.0.hash,
            self.0.range,
            self.0.bytes.len()
        )
    }

    fn __richcmp__(&self, other: &Self, op: CompareOp) -> bool {
        op.matches(self.0.cmp(&other.0))
    }

    fn __hash__(&self) -> u64 {
        hash_value(&self.0)
    }
}

/// An opaque checked fact about one byte range of a CAS blob.
///
/// Only this module's checking rules construct one: deriving it from a fact
/// that already covers those bytes, joining two such facts, or checking a
/// range proof.
#[pyclass(frozen, module = "covalence.cas", name = "CasRangeFact")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyCasRangeFact(CasRangeFact<BlobSpan>);

impl PyCasRangeFact {
    fn wrap(python: Python<'_>, fact: CasRangeFact<BlobSpan>) -> PyResult<Py<Self>> {
        Py::new(python, Self(fact))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCasRangeFact {
    /// Checked content address of the complete blob.
    #[getter]
    fn hash(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.hash())
    }

    /// First byte offset the range covers.
    #[getter]
    const fn start(&self) -> u64 {
        self.0.range().start()
    }

    /// One past the last byte, or `None` for the end of the blob.
    #[getter]
    const fn end(&self) -> Option<u64> {
        self.0.range().end()
    }

    /// Checked bytes at that range.
    #[getter]
    fn bytes<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, self.0.bytes())
    }

    /// The byte range these bytes occupy, as a `(start, end)` pair.
    ///
    /// This resolves an open upper bound, since the fact's bytes run to it.
    #[getter]
    fn extent(&self) -> (u64, u64) {
        let extent = self.0.extent();
        (extent.start, extent.end)
    }

    /// The blob's length, or `None` when this fact does not reach its end.
    ///
    /// A range with a closed end knows nothing about how long the blob is, so
    /// this answers `None` rather than mistaking the range's end for it. The
    /// data-free length claim is a fact whose `end` is `None` and whose bytes
    /// are empty.
    #[getter]
    fn blob_len(&self) -> Option<u64> {
        self.0.blob_len()
    }

    /// Narrows this fact to a sub-range of the bytes it already knows.
    ///
    /// Offsets are absolute, not relative to this fact. An `end` of `None`
    /// asks for the end of the blob, which only a fact already reaching it
    /// can answer.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when the request is not contained in this fact.
    #[pyo3(signature = (start, end = None))]
    fn slice(&self, python: Python<'_>, start: u64, end: Option<u64>) -> PyResult<Py<Self>> {
        let fact = self
            .0
            .slice(span(start, end)?)
            .map_err(|error| range_error(&error))?;
        Self::wrap(python, fact)
    }

    /// Joins this fact with another about the same blob.
    ///
    /// The ranges must overlap or touch; a gap would leave bytes the union
    /// claims to know but neither operand does.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when the facts are about different blobs or
    /// their ranges leave a gap.
    fn fuse(&self, python: Python<'_>, other: PyRef<'_, Self>) -> PyResult<Py<Self>> {
        let fact = self.0.fuse(&other.0).map_err(|error| range_error(&error))?;
        Self::wrap(python, fact)
    }

    /// Returns this fact as a whole-blob fact.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` unless the range starts at zero and reaches the
    /// end of the blob.
    fn whole(&self, python: Python<'_>) -> PyResult<Py<PyCasFact>> {
        let fact = self.0.slice(..).map_err(|error| range_error(&error))?;
        PyCasFact::wrap(python, fact)
    }

    /// Returns the underlying assertion, forgetting checkedness.
    #[getter]
    fn assertion(&self) -> PyCasRangeAssertion {
        PyCasRangeAssertion::wrap(CasRangeAssertion::from(&self.0))
    }

    fn __repr__(&self) -> String {
        format!(
            "CasRangeFact(hash=O256.from_hex('{}'), range={}, bytes_len={})",
            self.0.hash(),
            self.0.range(),
            self.0.bytes().len()
        )
    }

    fn __richcmp__(&self, other: &Self, op: CompareOp) -> bool {
        op.matches(self.0.cmp(&other.0))
    }

    fn __hash__(&self) -> u64 {
        hash_value(&self.0)
    }
}

/// The chaining values a byte range needs to reach its blob's root.
///
/// Ordinary unchecked data. Level `l` views the blob in blocks of
/// `1024 << l` bytes; the spines are the siblings met while climbing from the
/// range to the root, each a 32-byte chaining value.
#[pyclass(frozen, module = "covalence.cas", name = "RangeProof")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyRangeProof(RangeProof);

fn chaining_values(values: &Bound<'_, PyAny>) -> PyResult<Vec<Blake3Cv>> {
    values
        .try_iter()?
        .map(|value| {
            let bytes = value?.extract::<Bytes>()?;
            let array: [u8; 32] = bytes.as_slice().try_into().map_err(|_| {
                CasProofError::new_err(format!(
                    "chaining value must be 32 bytes, found {}",
                    bytes.as_slice().len()
                ))
            })?;
            Ok(Blake3Cv::from_array(array))
        })
        .collect()
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyRangeProof {
    /// Assembles a proof object without validating it.
    ///
    /// # Errors
    ///
    /// Raises `CasProofError` when a chaining value is not 32 bytes.
    #[new]
    fn new(level: u32, left: &Bound<'_, PyAny>, right: &Bound<'_, PyAny>) -> PyResult<Self> {
        Ok(Self(RangeProof::new(
            level,
            chaining_values(left)?,
            chaining_values(right)?,
        )))
    }

    /// Derives the proof that a range of `blob` sits under `blob`'s root.
    ///
    /// This is untrusted userspace: what it produces still has to pass
    /// `check`.
    ///
    /// # Errors
    ///
    /// Raises `CasProofError` when the level is too large, the range is not
    /// aligned to that level's blocks, or the range is empty or past the end
    /// of `blob`.
    #[staticmethod]
    #[pyo3(signature = (level, start, end, blob))]
    fn prove(
        python: Python<'_>,
        level: u32,
        start: u64,
        end: Option<u64>,
        blob: Bytes,
    ) -> PyResult<Self> {
        let range = span(start, end)?;
        let proof = python
            .detach(|| RangeProof::prove(level, &range, blob.as_slice()))
            .map_err(|error| proof_error(&error))?;
        Ok(Self(proof))
    }

    /// Tree level the spines are taken at.
    #[getter]
    const fn level(&self) -> u32 {
        self.0.level()
    }

    /// Number of bytes in one block at this proof's level.
    #[getter]
    const fn block_len(&self) -> Option<u64> {
        self.0.block_len()
    }

    /// Chaining values left of the range, widest first.
    #[getter]
    fn left<'py>(&self, python: Python<'py>) -> Vec<Bound<'py, PyBytes>> {
        self.0
            .left()
            .iter()
            .map(|cv| PyBytes::new(python, cv.as_bytes()))
            .collect()
    }

    /// Chaining values right of the range, in climbing order.
    #[getter]
    fn right<'py>(&self, python: Python<'py>) -> Vec<Bound<'py, PyBytes>> {
        self.0
            .right()
            .iter()
            .map(|cv| PyBytes::new(python, cv.as_bytes()))
            .collect()
    }

    /// Checks that `bytes` are the given range of the blob at `hash`.
    ///
    /// # Errors
    ///
    /// Raises `CasProofError` when the range is unusable at this level or the
    /// spines do not describe a tree, and `CasDigestMismatchError` when the
    /// rebuilt root is not `hash`.
    #[pyo3(signature = (hash, start, end, bytes))]
    fn check(
        &self,
        python: Python<'_>,
        hash: PyRef<'_, PyO256>,
        start: u64,
        end: Option<u64>,
        bytes: Bytes,
    ) -> PyResult<Py<PyCasRangeFact>> {
        let hash = PyO256::value(&hash);
        let range = span(start, end)?;
        let bytes = CasBytes::copy_from_slice(bytes.as_slice());
        let fact = python
            .detach(|| self.0.check(hash, range, bytes))
            .map_err(|error| proof_error(&error))?;
        PyCasRangeFact::wrap(python, fact)
    }

    fn __repr__(&self) -> String {
        format!(
            "RangeProof(level={}, left={}, right={})",
            self.0.level(),
            self.0.left().len(),
            self.0.right().len()
        )
    }
}

/// An insertion-ordered userspace CAS with stable integer IDs.
#[pyclass(module = "covalence.cas", name = "IndexCas")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyIndexCas(IndexCas);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyIndexCas {
    #[new]
    fn new() -> Self {
        Self(IndexCas::new())
    }

    /// Hashes and inserts complete bytes, returning their stable ID.
    fn put(&mut self, blob: Bytes) -> u64 {
        self.0.insert(CasBytes::copy_from_slice(blob.as_slice()))
    }

    /// Inserts a checked fact, returning its stable ID.
    fn insert(&mut self, fact: PyRef<'_, PyCasFact>) -> u64 {
        self.0.insert_fact(fact.0.clone())
    }

    /// Returns the stable ID for an address, if resident.
    fn id(&self, address: PyRef<'_, PyO256>) -> Option<u64> {
        self.0.id(PyO256::value(&address))
    }

    /// Hashes bytes and returns the stable ID of their address, if resident.
    fn id_bytes(&self, blob: Bytes) -> Option<u64> {
        self.0.id_bytes(blob.as_slice())
    }

    /// Returns the fact at an integer ID, if resident.
    fn fact(&self, python: Python<'_>, id: u64) -> PyResult<Option<Py<PyCasFact>>> {
        self.0
            .fact(id)
            .cloned()
            .map(|fact| PyCasFact::wrap(python, fact))
            .transpose()
    }

    /// Returns raw bytes for an address.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when the address is absent.
    fn get<'py>(
        &self,
        python: Python<'py>,
        address: PyRef<'_, PyO256>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let address = PyO256::value(&address);
        let fact = self
            .0
            .fact_at(address)
            .ok_or_else(|| CasNotFoundError::new_err(address.to_string()))?;
        Ok(PyBytes::new(python, fact.bytes()))
    }

    /// Returns the checked fact for an address.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when the address is absent.
    fn get_fact(&self, python: Python<'_>, address: PyRef<'_, PyO256>) -> PyResult<Py<PyCasFact>> {
        let address = PyO256::value(&address);
        let fact = self
            .0
            .fact_at(address)
            .cloned()
            .ok_or_else(|| CasNotFoundError::new_err(address.to_string()))?;
        PyCasFact::wrap(python, fact)
    }

    /// Returns whether an address is resident.
    fn contains(&self, address: PyRef<'_, PyO256>) -> bool {
        self.0.id(PyO256::value(&address)).is_some()
    }

    /// Removes an address without changing any other fact ID.
    fn remove(&mut self, address: PyRef<'_, PyO256>) -> bool {
        self.0.remove(PyO256::value(&address))
    }

    /// Returns all `(id, fact)` pairs in insertion order.
    fn items(&self, python: Python<'_>) -> PyResult<Vec<(u64, Py<PyCasFact>)>> {
        self.0
            .facts()
            .map(|(id, fact)| Ok((id, PyCasFact::wrap(python, fact.clone())?)))
            .collect()
    }

    fn __len__(&self) -> usize {
        self.0.fact_count()
    }
}

/// Gets a checked fact from an arbitrary Python CAS.
///
/// Providers may optimize `get_fact(address) -> CasFact`; otherwise their
/// `get(address)` method must return raw bytes, which are hashed here. Provider
/// exceptions propagate unchanged.
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "get_checked")]
fn get_checked_python(
    python: Python<'_>,
    provider: Py<PyAny>,
    address: PyRef<'_, PyO256>,
) -> PyResult<Py<PyCasFact>> {
    let requested = PyO256::value(&address);
    let provider = provider.bind(python);
    let address = PyO256::wrap(python, requested)?;

    if provider.hasattr("get_fact")? {
        let returned = provider.call_method1("get_fact", (address,))?;
        let fact = returned.extract::<PyRef<'_, PyCasFact>>()?;
        let fact = fact.0.clone();
        if fact.hash() != requested {
            return Err(CasAddressMismatchError::new_err(format!(
                "CAS returned address {} for request {requested}",
                fact.hash()
            )));
        }
        return PyCasFact::wrap(python, fact);
    }

    let returned = provider.call_method1("get", (address,))?;
    let blob = returned.extract::<Bytes>()?;
    let blob = CasBytes::copy_from_slice(blob.as_slice());
    let fact = python
        .detach(|| CasFact::new(requested, blob))
        .map_err(check_error)?;
    PyCasFact::wrap(python, fact)
}

/// Adds the whole-object CAS API to the extension module.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCasAssertion>()?;
    module.add_class::<PyCasFact>()?;
    module.add_class::<PyCasRangeAssertion>()?;
    module.add_class::<PyCasRangeFact>()?;
    module.add_class::<PyRangeProof>()?;
    module.add_class::<PyIndexCas>()?;

    let python = module.py();
    for (name, exception) in [
        ("CasCheckError", PyType::new::<CasCheckError>(python)),
        (
            "CasDigestMismatchError",
            PyType::new::<CasDigestMismatchError>(python),
        ),
        ("CasRangeError", PyType::new::<CasRangeError>(python)),
        ("CasProofError", PyType::new::<CasProofError>(python)),
        ("CasLookupError", PyType::new::<CasLookupError>(python)),
        ("CasNotFoundError", PyType::new::<CasNotFoundError>(python)),
        (
            "CasAddressMismatchError",
            PyType::new::<CasAddressMismatchError>(python),
        ),
    ] {
        exception.setattr("__module__", "covalence.cas")?;
        module.add(name, exception)?;
    }

    let function = wrap_pyfunction!(get_checked_python, module)?;
    function.setattr("__module__", "covalence.cas")?;
    module.add_function(function)
}
