//! Whole-object CAS facts and indexed userspace storage for Python.

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
use covalence_logic_cas::{Bytes as CasBytes, CasAssertion, CasFact};

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
    module.add_class::<PyIndexCas>()?;

    let python = module.py();
    for (name, exception) in [
        ("CasCheckError", PyType::new::<CasCheckError>(python)),
        (
            "CasDigestMismatchError",
            PyType::new::<CasDigestMismatchError>(python),
        ),
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
