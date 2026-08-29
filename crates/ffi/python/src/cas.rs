//! Whole-object and range CAS facts, the blob equality calculus over them, and
//! indexed userspace storage, for Python.

#![allow(clippy::needless_pass_by_value)]

use std::hash::{DefaultHasher, Hash, Hasher};

use covalence_data_cas::IndexCas;
use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    basic::CompareOp,
    exceptions::{PyLookupError, PyTypeError},
    types::{PyBytes, PySlice, PyType},
};
use covalence_logic_cas::{
    Blake3Cv, BlobEq, BlobExpr, BlobFact, BlobProp, BlobSpan, Bytes as CasBytes, CasAssertion,
    CasFact, CasRangeAssertion, CasRangeFact, RangeProof,
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
    BlobRuleError,
    CasCheckError,
    "A blob-equality rule did not apply."
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

/// Reads one bound of a Python slice as an absolute offset.
///
/// # Errors
///
/// Raises `CasRangeError` for a negative bound. Offsets here are absolute
/// `u64`s, so `blob[-3:]` would have to be resolved against a length, and a
/// blob expression need not have one.
fn offset(value: &Bound<'_, PyAny>, name: &str) -> PyResult<Option<u64>> {
    if value.is_none() {
        return Ok(None);
    }
    value.extract::<u64>().map(Some).map_err(|_| {
        CasRangeError::new_err(format!(
            "slice {name} must be an offset in 0 .. 2 ** 64: blob offsets are \
             absolute, so counting back from the end would need a length that \
             a blob expression need not have"
        ))
    })
}

/// Reads a Python slice as the one span shape the calculus has.
///
/// `blob[3:7]`, `blob[3:]`, `blob[:7]` and `blob[:]` are the four forms, and
/// `blob[:]` is the whole-blob span that normalises away.
///
/// # Errors
///
/// Raises `TypeError` for a position rather than a slice, since a single byte
/// of a blob expression is a one-byte expression rather than an `int`, and
/// `CasRangeError` for a step, a negative bound, or a backwards span.
fn getitem_span(key: &Bound<'_, PyAny>) -> PyResult<BlobSpan> {
    let Ok(slice) = key.cast::<PySlice>() else {
        return Err(PyTypeError::new_err(
            "a blob is indexed by a slice, not by a position: one byte is \
             blob[i:i + 1], which is a one-byte blob rather than an int",
        ));
    };
    if !slice.getattr("step")?.is_none() {
        return Err(CasRangeError::new_err(
            "a blob slice takes no step: a stride is not a sub-range, and the \
             calculus has no expression denoting one",
        ));
    }
    let start = offset(&slice.getattr("start")?, "start")?.unwrap_or_default();
    span(start, offset(&slice.getattr("stop")?, "stop")?)
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

    /// Reads this fact as a blob-expression equality, `Blake3(h) = Bytes(b)`.
    ///
    /// The bridge up into the equality calculus. It is an ordinary rule and it
    /// is total: a model of the CAS agrees with every checked pair by
    /// definition, so the equality holds in every one of them.
    fn to_blob_fact(&self, python: Python<'_>) -> PyResult<Py<PyBlobFact>> {
        PyBlobFact::wrap(python, self.0.to_blob_fact().erase())
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

    /// Reads this fact as a blob-expression equality.
    ///
    /// A whole-blob range comes out as `Blake3(h) = Bytes(b)`, since the
    /// whole-blob span normalises away; `3..9` comes out as
    /// `Slice(Blake3(h), 3..9) = Bytes(b)`. `BlobFact.to_range_fact` reads
    /// either shape back.
    ///
    /// The bridge up into the equality calculus. It is an ordinary rule and it
    /// is total: a model of the CAS agrees with every checked pair by
    /// definition, so the equality holds in every one of them.
    fn to_blob_fact(&self, python: Python<'_>) -> PyResult<Py<PyBlobFact>> {
        PyBlobFact::wrap(python, self.0.to_blob_fact().erase())
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

/// The largest expression `__repr__` spells out in full, counted as a tree.
///
/// A `Cat` may denote a tree of `2^64` nodes, so nothing that has to be cheap
/// may recurse without a bound. The guard is O(1) — `size` is memoised at every
/// branching node — so a hyperblob costs a summary and nothing more, and the
/// small expressions people actually type print in full.
const MAX_REPR_NODES: u32 = 32;

/// The longest byte string `__repr__` spells out in full.
const MAX_REPR_BYTES: usize = 32;

/// Renders literal bytes as the call that rebuilds them.
fn bytes_repr(bytes: &[u8]) -> String {
    if bytes.len() > MAX_REPR_BYTES {
        return format!("BlobExpr.bytes(len={})", bytes.len());
    }
    let mut text = String::from("BlobExpr.bytes(b'");
    for byte in bytes {
        text.extend(std::ascii::escape_default(*byte).map(char::from));
    }
    text.push_str("')");
    text
}

/// Renders an expression's root node alone, for a tree too big to walk.
fn expr_summary(expr: &BlobExpr) -> String {
    match expr {
        BlobExpr::Cat(_) => format!("BlobExpr.cat(size={})", expr.size()),
        BlobExpr::Slice(slice) => format!(
            "BlobExpr.slice(span={}, size={})",
            slice.span(),
            expr.size()
        ),
        // Every leaf is one node, so only the branching variants reach this.
        // `BlobExpr` is `#[non_exhaustive]`, so a variant added upstream lands
        // here rather than breaking this build.
        _ => format!("BlobExpr(size={})", expr.size()),
    }
}

/// Renders an expression as the calls that rebuild it, down to a bounded depth.
///
/// Round-trips for anything inside the bound: what comes back is Python that
/// evaluates to an equal expression, given `BlobExpr` and `O256` in scope.
/// Past the bound, and past [`MAX_REPR_BYTES`] of literal bytes, it summarises
/// rather than growing without limit.
fn expr_repr(expr: &BlobExpr) -> String {
    if expr.size() > MAX_REPR_NODES {
        return expr_summary(expr);
    }
    match expr {
        BlobExpr::Blake3(hash) => format!("BlobExpr.blake3(O256.from_hex('{hash}'))"),
        BlobExpr::Bytes(bytes) => bytes_repr(bytes),
        BlobExpr::Zero(count) => format!("BlobExpr.zero({count})"),
        BlobExpr::Cat(cat) => format!(
            "BlobExpr.cat({}, {})",
            expr_repr(cat.left()),
            expr_repr(cat.right())
        ),
        BlobExpr::Slice(slice) => slice.span().end().map_or_else(
            || {
                format!(
                    "BlobExpr.slice({}, {})",
                    expr_repr(slice.blob()),
                    slice.span().start()
                )
            },
            |end| {
                format!(
                    "BlobExpr.slice({}, {}, {end})",
                    expr_repr(slice.blob()),
                    slice.span().start()
                )
            },
        ),
        _ => expr_summary(expr),
    }
}

/// Hashes an expression's root node and its tree size, and nothing deeper.
///
/// Sound as a Python `__hash__` because both are functions of the tree that
/// `==` compares: equal expressions have the same variant, the same leaf
/// payload and the same size, so they hash alike. Deliberately shallow, so
/// that hashing a hyperblob is O(1) where comparing two is not.
fn hash_expr(expr: &BlobExpr) -> u64 {
    let mut hasher = DefaultHasher::new();
    expr.size().hash(&mut hasher);
    match expr {
        BlobExpr::Blake3(hash) => (0_u8, hash).hash(&mut hasher),
        BlobExpr::Bytes(bytes) => (1_u8, &bytes[..]).hash(&mut hasher),
        BlobExpr::Zero(count) => (2_u8, count).hash(&mut hasher),
        BlobExpr::Cat(_) => 3_u8.hash(&mut hasher),
        BlobExpr::Slice(slice) => (4_u8, slice.span()).hash(&mut hasher),
        // A variant added upstream hashes on its size alone, which still
        // agrees with `==`: that only ever compares two of the same variant.
        _ => 5_u8.hash(&mut hasher),
    }
    hasher.finish()
}

/// The one erased proposition Python sees, `BlobExpr = BlobExpr`.
type ErasedEq = BlobEq<BlobExpr, BlobExpr>;

/// An expression denoting a byte string.
///
/// Syntax, not bytes. What an expression means is a partial function of a
/// *model*: a total, injective map from every `O256` to bytes that agrees with
/// the CAS wherever the CAS is defined. Two expressions are equal when they
/// denote the same thing in every model.
///
/// `BlobExpr.blake3(h)` is the blob **named by** `h`, never the 32 bytes of
/// the digest itself; those are `BlobExpr.bytes(bytes(h))`, and nothing here
/// relates the two. A digest denotes some byte string in every model, but not
/// the same one in all of them, which is why it has neither a `len_bytes` nor
/// an `eval` here.
///
/// Every constructor is total. `cat` shares its operands, so a short chain of
/// them can denote an astronomically large tree; `size` counts that tree, and
/// the observations below answer `None` rather than walking one past 1024
/// nodes. Declining is always a sound answer.
///
/// `left + right` is `cat` and `blob[3:7]` is `slice`, so the two structural
/// constructors read the way the bytes they denote would. Indexing stops
/// there: there is deliberately no `len()`, because `__len__` must return an
/// `int` and this length is three-valued, so `len()` would have to raise
/// exactly where `len_bytes` answers `None` — and, `__len__` being what
/// `bool()` falls back on, `if blob:` would raise with it. It could not report
/// the known cases either, since a `__len__` is capped at `sys.maxsize` while
/// `BlobExpr.zero(2 ** 64 - 1)` has a perfectly definite length. `len_bytes`
/// is the total accessor, and it is the only one.
#[pyclass(frozen, module = "covalence.cas", name = "BlobExpr")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyBlobExpr(BlobExpr);

impl PyBlobExpr {
    fn wrap(python: Python<'_>, expr: BlobExpr) -> PyResult<Py<Self>> {
        Py::new(python, Self(expr))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyBlobExpr {
    /// The blob named by a content address.
    ///
    /// Not the digest's own 32 bytes. Those are
    /// `BlobExpr.bytes(bytes(hash))`, and no rule relates the two.
    #[staticmethod]
    fn blake3(python: Python<'_>, hash: PyRef<'_, PyO256>) -> PyResult<Py<Self>> {
        Self::wrap(python, BlobExpr::Blake3(PyO256::value(&hash)))
    }

    /// Literal bytes.
    #[staticmethod]
    fn bytes(python: Python<'_>, blob: Bytes) -> PyResult<Py<Self>> {
        let blob = CasBytes::copy_from_slice(blob.as_slice());
        Self::wrap(python, BlobExpr::Bytes(blob))
    }

    /// A run of `length` zero bytes.
    #[staticmethod]
    fn zero(python: Python<'_>, length: u64) -> PyResult<Py<Self>> {
        Self::wrap(python, BlobExpr::Zero(length))
    }

    /// Two expressions concatenated. Total, and O(1): the operands are shared
    /// rather than copied.
    #[staticmethod]
    fn cat(
        python: Python<'_>,
        left: PyRef<'_, Self>,
        right: PyRef<'_, Self>,
    ) -> PyResult<Py<Self>> {
        Self::wrap(python, BlobExpr::cat(left.0.clone(), right.0.clone()))
    }

    /// A sub-range of another expression, in that expression's coordinates.
    ///
    /// An `end` of `None` runs to the end of the sliced expression, so
    /// `slice(e, 0)` normalises to `e` itself. Out of range denotes nothing at
    /// all; it is never clamped, so `len_bytes` and `eval` answer `None`
    /// rather than truncating.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when `end` precedes `start`.
    #[staticmethod]
    #[pyo3(signature = (blob, start, end = None))]
    fn slice(
        python: Python<'_>,
        blob: PyRef<'_, Self>,
        start: u64,
        end: Option<u64>,
    ) -> PyResult<Py<Self>> {
        let expr = BlobExpr::slice(blob.0.clone(), span(start, end)?);
        Self::wrap(python, expr)
    }

    /// The length of the byte string this denotes, or `None` when no `u64`
    /// answers it in every model.
    ///
    /// `None` is neither zero nor an error. It means the length is unknown:
    /// behind a digest, out of range on a slice, past `u64` on a sum, or past
    /// the 1024-node limit this declines to walk.
    #[getter]
    fn len_bytes(&self) -> Option<u64> {
        self.0.len()
    }

    /// The node count of this expression viewed as a tree, never as a DAG.
    ///
    /// Saturates at `2 ** 32 - 1`, where it reads as "at least this big". The
    /// observations decline past 1024.
    #[getter]
    const fn size(&self) -> u32 {
        self.0.size()
    }

    /// The bytes this denotes, or `None` when the models disagree or the work
    /// is refused.
    ///
    /// `None` for anything behind a digest, for an out-of-range slice, past a
    /// gibibyte of output, and past the 1024-node limit. It is not an error:
    /// declining is the normal sound answer.
    fn eval<'py>(&self, python: Python<'py>) -> Option<Bound<'py, PyBytes>> {
        let bytes = python.detach(|| self.0.eval())?;
        Some(PyBytes::new(python, &bytes))
    }

    /// `left + right` is `BlobExpr.cat(left, right)`.
    ///
    /// Both operands must already be expressions. A `bytes` operand is not
    /// coerced, because `BlobExpr.bytes(b)` and `BlobExpr.blake3(h)` are the
    /// two different readings of a 32-byte value and a coercion would have to
    /// guess one.
    fn __add__(&self, python: Python<'_>, other: PyRef<'_, Self>) -> PyResult<Py<Self>> {
        Self::wrap(python, BlobExpr::cat(self.0.clone(), other.0.clone()))
    }

    /// `blob[3:7]` is `BlobExpr.slice(blob, 3, 7)`, and `blob[3:]` is the open
    /// case that runs to the end of `blob`.
    ///
    /// Not quite `bytes`, in the two places the calculus disagrees with it.
    /// Offsets are absolute and never counted back from an end that may be
    /// unknown, and an out-of-range or backwards span is never quietly
    /// narrowed to what is there: `blob[5:9]` of a two-byte expression denotes
    /// nothing at all rather than `b""`.
    ///
    /// # Errors
    ///
    /// Raises `TypeError` for a position rather than a slice, and
    /// `CasRangeError` for a step, a negative bound, or a backwards span.
    fn __getitem__(&self, python: Python<'_>, key: &Bound<'_, PyAny>) -> PyResult<Py<Self>> {
        let expr = BlobExpr::slice(self.0.clone(), getitem_span(key)?);
        Self::wrap(python, expr)
    }

    fn __repr__(&self) -> String {
        expr_repr(&self.0)
    }

    /// Structural equality, which walks both trees in full.
    ///
    /// Unbounded on purpose: a limit here would change what equality means.
    /// `BlobEq.decide` is the bounded question, and it declines before it ever
    /// compares a hyperblob.
    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __hash__(&self) -> u64 {
        hash_expr(&self.0)
    }
}

/// The unchecked claim that two expressions denote the same byte string.
///
/// Ordinary data with public `lhs` and `rhs`, like `CasRangeAssertion`. The
/// trust boundary is `BlobFact`, which only the rules can build.
#[pyclass(frozen, module = "covalence.cas", name = "BlobEq")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyBlobEq(ErasedEq);

impl PyBlobEq {
    fn wrap(python: Python<'_>, prop: ErasedEq) -> PyResult<Py<Self>> {
        Py::new(python, Self(prop))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyBlobEq {
    /// Claims that `lhs` and `rhs` denote the same byte string. Unchecked.
    #[new]
    fn new(lhs: PyRef<'_, PyBlobExpr>, rhs: PyRef<'_, PyBlobExpr>) -> Self {
        Self(BlobEq::new(lhs.0.clone(), rhs.0.clone()))
    }

    /// The left-hand expression.
    #[getter]
    fn lhs(&self, python: Python<'_>) -> PyResult<Py<PyBlobExpr>> {
        PyBlobExpr::wrap(python, self.0.lhs.clone())
    }

    /// The right-hand expression.
    #[getter]
    fn rhs(&self, python: Python<'_>) -> PyResult<Py<PyBlobExpr>> {
        PyBlobExpr::wrap(python, self.0.rhs.clone())
    }

    /// Decides this equality, when the rules settle it.
    ///
    /// `True` means it holds in every model, `False` that it fails in every
    /// model, and `None` that the rules do not settle it. `None` is never an
    /// error: it covers an unresolvable digest, an unknown length, and a
    /// traversal declining past the 1024-node limit, all of which are the
    /// normal sound answer rather than a failure.
    fn decide(&self, python: Python<'_>) -> Option<bool> {
        python.detach(|| self.0.decide())
    }

    fn __repr__(&self) -> String {
        format!(
            "BlobEq(lhs={}, rhs={})",
            expr_repr(&self.0.lhs),
            expr_repr(&self.0.rhs)
        )
    }

    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __hash__(&self) -> u64 {
        hash_value(&(hash_expr(&self.0.lhs), hash_expr(&self.0.rhs)))
    }
}

/// A checked equality between blob expressions: the LCF boundary.
///
/// Holding one is holding a proof that its proposition is valid in every
/// model. Only the rules below build one — `refl`, `symm`, `trans`, `cat`,
/// `slice`, `erase`, `check`, and the bridge from a `CasRangeFact` — so, like
/// `CasRangeFact`, this has no constructor, cannot be subclassed, cannot be
/// unpickled back into existence, and has no mutable field.
///
/// Python holds the erased form, `BlobExpr = BlobExpr`, because it cannot
/// carry Rust's operand type parameters. That is the same erasure that makes
/// `CasRangeFact` carry `start` and `end` instead of a range type.
#[pyclass(frozen, module = "covalence.cas", name = "BlobFact")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyBlobFact(BlobFact<ErasedEq>);

impl PyBlobFact {
    fn wrap(python: Python<'_>, fact: BlobFact<ErasedEq>) -> PyResult<Py<Self>> {
        Py::new(python, Self(fact))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyBlobFact {
    /// RULE: EVALUATION. Checks a proposition and introduces a fact when the
    /// decision procedure proves it.
    ///
    /// # Errors
    ///
    /// Raises `BlobRuleError` when the proposition is refuted, and also when
    /// the rules simply do not settle it. Neither is a fact. Call
    /// `BlobEq.decide` to tell the two apart without an exception.
    #[staticmethod]
    fn check(python: Python<'_>, prop: PyRef<'_, PyBlobEq>) -> PyResult<Py<Self>> {
        let prop = prop.0.clone();
        let checked = python.detach(|| BlobFact::check(prop.clone()));
        let Some(fact) = checked else {
            return Err(BlobRuleError::new_err(
                if python.detach(|| prop.decide()) == Some(false) {
                    "the equality is refuted, and a refutation is not a fact"
                } else {
                    "the rules do not settle this equality"
                },
            ));
        };
        Self::wrap(python, fact)
    }

    /// RULE: REFL. Total.
    ///
    /// Needs no length, no bytes and no definedness, so it holds for a digest
    /// this crate cannot resolve, for an out-of-range slice, and for an
    /// expression too large for `BlobEq.decide` to say anything about.
    #[staticmethod]
    fn refl(python: Python<'_>, blob: PyRef<'_, PyBlobExpr>) -> PyResult<Py<Self>> {
        Self::wrap(python, BlobFact::refl(blob.0.clone()))
    }

    /// The proposition this fact establishes.
    #[getter]
    fn prop(&self, python: Python<'_>) -> PyResult<Py<PyBlobEq>> {
        PyBlobEq::wrap(python, self.0.prop().clone())
    }

    /// RULE: SYMM. Total.
    fn symm(&self, python: Python<'_>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.symm())
    }

    /// RULE: TRANS. Composes two facts sharing a middle expression.
    ///
    /// # Errors
    ///
    /// Raises `BlobRuleError` when this fact's right-hand side is not the same
    /// expression as `next`'s left-hand side. Nothing in the types supplies
    /// that check, so without it `a = b` and `c = d` would compose into
    /// `a = d`.
    fn trans(&self, python: Python<'_>, next: PyRef<'_, Self>) -> PyResult<Py<Self>> {
        let fact = self
            .0
            .trans(&next.0)
            .ok_or_else(|| BlobRuleError::new_err("the middle terms are different expressions"))?;
        Self::wrap(python, fact)
    }

    /// RULE: CONGRUENCE, for concatenation. Total. Spelled `head + tail`.
    ///
    /// Equality only. Unequal operands say nothing about the wholes, since
    /// `cat("ab", "c")` and `cat("a", "bc")` are equal, so there is no
    /// converse and none may be added.
    fn cat(&self, python: Python<'_>, tail: PyRef<'_, Self>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.cat(&tail.0).erase())
    }

    /// RULE: CONGRUENCE, for slicing. Total.
    ///
    /// One span for both sides, so the unsound shape — equal subjects sliced
    /// differently — is not expressible.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` when `end` precedes `start`.
    #[pyo3(signature = (start, end = None))]
    fn slice(&self, python: Python<'_>, start: u64, end: Option<u64>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.slice(span(start, end)?).erase())
    }

    /// Reifies both sides, keeping the claim. Total.
    ///
    /// The identity here, since Python only ever holds the erased form: Rust
    /// uses it to bring facts over differing carrier types together, and it is
    /// exposed so that a rule's name means the same thing on both sides of the
    /// boundary.
    fn erase(&self, python: Python<'_>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.erase())
    }

    /// Recovers a range fact from an equality that has a range fact's shape.
    ///
    /// The bridge back down. Ordinary, exactly like `to_blob_fact` going up:
    /// an equality about `Blake3(h)` can only hold in every model when the CAS
    /// pins `h`, so the premise already says what a `CasRangeFact` asserts.
    ///
    /// # Errors
    ///
    /// Raises `CasRangeError` unless the left side is a digest or a slice of
    /// one, the right side is literal bytes, and a closed span agrees with
    /// those bytes' width. Use `symm` first for the mirrored shape.
    fn to_range_fact(&self, python: Python<'_>) -> PyResult<Py<PyCasRangeFact>> {
        let fact = self.0.to_range_fact::<BlobSpan>().ok_or_else(|| {
            CasRangeError::new_err("this equality does not have a range fact's shape")
        })?;
        PyCasRangeFact::wrap(python, fact)
    }

    /// `head + tail` is `head.cat(tail)`, the same congruence rule.
    ///
    /// The operand order is the order the bytes appear in, so this is
    /// concatenation of what the facts are about rather than any joining of
    /// the facts themselves: from `a = b` and `c = d` it concludes
    /// `cat(a, c) = cat(b, d)`, and it says nothing whatever about `a = c`.
    fn __add__(&self, python: Python<'_>, tail: PyRef<'_, Self>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.cat(&tail.0).erase())
    }

    /// `fact[3:7]` is `fact.slice(3, 7)`, the same congruence rule.
    ///
    /// One span for both sides, exactly as in the method: slicing a proof
    /// yields the proof about the slices, and the unsound shape — equal
    /// subjects sliced differently — is not expressible either way.
    ///
    /// # Errors
    ///
    /// Raises `TypeError` for a position rather than a slice, and
    /// `CasRangeError` for a step, a negative bound, or a backwards span.
    fn __getitem__(&self, python: Python<'_>, key: &Bound<'_, PyAny>) -> PyResult<Py<Self>> {
        Self::wrap(python, self.0.slice(getitem_span(key)?).erase())
    }

    fn __repr__(&self) -> String {
        format!(
            "BlobFact(lhs={}, rhs={})",
            expr_repr(&self.0.prop().lhs),
            expr_repr(&self.0.prop().rhs)
        )
    }

    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __hash__(&self) -> u64 {
        let prop = self.0.prop();
        hash_value(&(hash_expr(&prop.lhs), hash_expr(&prop.rhs)))
    }
}

/// An insertion-ordered userspace CAS with stable integer IDs.
///
/// It stores whole blobs, because that is what a content address names, but it
/// answers about ranges: `range` derives a checked range fact, `prove` derives
/// the range proof a holder of no bytes at all would need, and `blob_fact`
/// hands a stored blob to the equality calculus.
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

    /// Returns a checked range fact about a resident blob.
    ///
    /// Offsets are absolute, and an `end` of `None` runs to the end of the
    /// blob, so the result also knows the blob's length. This is `get_fact`
    /// followed by `CasFact.range`, without copying the whole blob into Python
    /// on the way past.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when the address is absent, and
    /// `CasRangeError` when the range is not within the blob.
    #[pyo3(signature = (address, start, end = None))]
    fn range(
        &self,
        python: Python<'_>,
        address: PyRef<'_, PyO256>,
        start: u64,
        end: Option<u64>,
    ) -> PyResult<Py<PyCasRangeFact>> {
        let address = PyO256::value(&address);
        let fact = self
            .0
            .fact_at(address)
            .ok_or_else(|| CasNotFoundError::new_err(address.to_string()))?;
        let fact = fact
            .slice(span(start, end)?)
            .map_err(|error| range_error(&error))?;
        PyCasRangeFact::wrap(python, fact)
    }

    /// Derives a range proof for a resident blob.
    ///
    /// Untrusted userspace, exactly like `RangeProof.prove`: the store is
    /// merely where the bytes are, and what comes back still has to pass
    /// `check` before it is a fact. A store that already keeps chaining-value
    /// trees would answer this without rehashing; this one rehashes.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when the address is absent, and
    /// `CasProofError` when the range is not usable at that level.
    #[pyo3(signature = (address, level, start, end = None))]
    fn prove(
        &self,
        python: Python<'_>,
        address: PyRef<'_, PyO256>,
        level: u32,
        start: u64,
        end: Option<u64>,
    ) -> PyResult<PyRangeProof> {
        let address = PyO256::value(&address);
        let range = span(start, end)?;
        let blob = self
            .0
            .fact_at(address)
            .ok_or_else(|| CasNotFoundError::new_err(address.to_string()))?
            .bytes()
            .clone();
        let proof = python
            .detach(|| RangeProof::prove(level, &range, &blob))
            .map_err(|error| proof_error(&error))?;
        Ok(PyRangeProof(proof))
    }

    /// Reads a resident blob as a blob-expression equality,
    /// `Blake3(h) = Bytes(b)`.
    ///
    /// The store's entry into the equality calculus. Resolving a digest is
    /// exactly what `BlobExpr` alone cannot do, since nothing in it reads a
    /// store; this is `get_fact(address).to_blob_fact()`, spelled from the
    /// side that has the bytes.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when the address is absent.
    fn blob_fact(
        &self,
        python: Python<'_>,
        address: PyRef<'_, PyO256>,
    ) -> PyResult<Py<PyBlobFact>> {
        let address = PyO256::value(&address);
        let fact = self
            .0
            .fact_at(address)
            .ok_or_else(|| CasNotFoundError::new_err(address.to_string()))?;
        PyBlobFact::wrap(python, fact.to_blob_fact().erase())
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

    /// `address in cas` is `cas.contains(address)`.
    ///
    /// Honest here in the way it would not be on `BlobExpr`: residency is a
    /// question this store always answers.
    fn __contains__(&self, address: PyRef<'_, PyO256>) -> bool {
        self.0.id(PyO256::value(&address)).is_some()
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
    module.add_class::<PyBlobExpr>()?;
    module.add_class::<PyBlobEq>()?;
    module.add_class::<PyBlobFact>()?;
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
        ("BlobRuleError", PyType::new::<BlobRuleError>(python)),
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
