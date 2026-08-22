//! Whole-object CAS facts and userspace providers at the Python boundary.
//!
//! Python may construct [`PyCasAssertion`] values, but only Rust's complete
//! blob checker can create [`PyCasFact`]. Stores and callbacks remain ordinary
//! userspace objects: their result is safe precisely because the checked fact
//! constructor is not available to them.

#![allow(clippy::needless_pass_by_value)]

use covalence_data_cas::{AdmissionError, MemoryCas, MemoryCasError};
use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    exceptions::{PyLookupError, PyRuntimeError},
    types::{PyBytes, PyType},
};
use covalence_logic_cas::{
    Bytes as CasBytes, CasAssertion, CasFact, GetError, InvalidCasAssertion, TrustedCas, get_exact,
};

use crate::hash::PyO256;

create_exception!(
    covalence,
    CasDigestMismatchError,
    PyValueError,
    "A whole-object CAS assertion carried the wrong content hash."
);
create_exception!(
    covalence,
    CasAddressMismatchError,
    PyValueError,
    "A CAS provider returned a checked fact for another address."
);
create_exception!(
    covalence,
    CasNotFoundError,
    PyLookupError,
    "A CAS provider does not contain the requested address."
);
create_exception!(
    covalence,
    CasCollisionError,
    PyRuntimeError,
    "A CAS address has distinct checked collision witnesses."
);
create_exception!(
    covalence,
    CasAdmissionError,
    PyValueError,
    "A CAS refused to admit a checked fact."
);

fn digest_error(error: InvalidCasAssertion) -> PyErr {
    CasDigestMismatchError::new_err(error.to_string())
}

fn admission_error(error: AdmissionError) -> PyErr {
    CasAdmissionError::new_err(error.to_string())
}

fn memory_error(error: MemoryCasError) -> PyErr {
    match error {
        MemoryCasError::Missing { .. } => CasNotFoundError::new_err(error.to_string()),
        MemoryCasError::Collision { .. } => CasCollisionError::new_err(error.to_string()),
    }
}

fn exact_memory_error(error: GetError<MemoryCasError>) -> PyErr {
    match error {
        GetError::Provider { source, .. } => memory_error(source),
        GetError::WrongAddress {
            requested,
            returned,
        } => CasAddressMismatchError::new_err(format!(
            "CAS returned address {returned} for request {requested}"
        )),
    }
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
        Self(CasAssertion {
            hash: PyO256::value(&hash),
            blob: CasBytes::copy_from_slice(blob.as_slice()),
        })
    }

    /// Claimed content address.
    #[getter]
    fn hash(&self, python: Python<'_>) -> PyResult<Py<PyO256>> {
        PyO256::wrap(python, self.0.hash)
    }

    /// Complete claimed bytes, copied into immutable Python `bytes`.
    #[getter]
    fn blob<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, &self.0.blob)
    }

    /// Hashes every byte and introduces a checked fact on success.
    ///
    /// # Errors
    ///
    /// Raises `CasDigestMismatchError` when the claimed address is wrong.
    fn try_into(&self, python: Python<'_>) -> PyResult<Py<PyCasFact>> {
        let assertion = self.0.clone();
        let fact = python
            .detach(|| CasFact::try_from(assertion))
            .map_err(digest_error)?;
        PyCasFact::wrap(python, fact)
    }

    fn __repr__(&self) -> String {
        format!(
            "CasAssertion(hash=O256.from_hex('{}'), blob_len={})",
            self.0.hash,
            self.0.blob.len()
        )
    }

    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __ne__(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

/// An opaque checked fact about a complete content-addressed blob.
///
/// There is deliberately no Python constructor. Use
/// [`PyCasAssertion::try_into`] or [`Self::from_bytes`].
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
    /// Hashes complete bytes and returns the resulting checked fact.
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

    /// Complete checked bytes, copied into immutable Python `bytes`.
    #[getter]
    fn blob<'py>(&self, python: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(python, self.0.bytes())
    }

    /// Forgets checkedness and returns an immutable assertion snapshot.
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

    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __ne__(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

/// A relation-style in-memory CAS backed by `Vec<CasFact>` and `HashTable`.
#[pyclass(module = "covalence.cas", name = "MemoryCas")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyMemoryCas(MemoryCas);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyMemoryCas {
    #[new]
    #[pyo3(signature = (limit=None))]
    fn new(limit: Option<u64>) -> Self {
        Self(limit.map_or_else(MemoryCas::new, MemoryCas::with_limit))
    }

    /// Largest blob this instance admits.
    #[getter]
    fn limit(&self) -> u64 {
        self.0.limit()
    }

    /// Hashes, checks, and admits complete bytes.
    ///
    /// # Errors
    ///
    /// Raises `CasAdmissionError` when `blob` exceeds this store's limit.
    fn put(&self, python: Python<'_>, blob: Bytes) -> PyResult<Py<PyCasFact>> {
        let blob = CasBytes::copy_from_slice(blob.as_slice());
        let fact = python.detach(|| CasFact::from_bytes(blob));
        self.0.insert_fact(fact.clone()).map_err(admission_error)?;
        PyCasFact::wrap(python, fact)
    }

    /// Admits a checked fact, returning whether it was a new relation member.
    ///
    /// # Errors
    ///
    /// Raises `CasAdmissionError` when the fact exceeds this store's limit.
    fn insert(&self, fact: PyRef<'_, PyCasFact>) -> PyResult<bool> {
        self.0.insert_fact(fact.0.clone()).map_err(admission_error)
    }

    /// Gets the unique checked fact for exactly `address`.
    ///
    /// # Errors
    ///
    /// Raises `CasNotFoundError` when absent and `CasCollisionError` when the
    /// address has distinct checked witnesses.
    fn get(&self, python: Python<'_>, address: PyRef<'_, PyO256>) -> PyResult<Py<PyCasFact>> {
        let fact = get_exact(&self.0, PyO256::value(&address)).map_err(exact_memory_error)?;
        PyCasFact::wrap(python, fact)
    }

    /// Returns whether at least one checked pair carries `address`.
    fn contains(&self, address: PyRef<'_, PyO256>) -> bool {
        self.0.contains(PyO256::value(&address))
    }

    /// Removes every fact carrying `address`.
    fn remove(&self, address: PyRef<'_, PyO256>) -> bool {
        self.0.remove(PyO256::value(&address))
    }

    /// Returns every checked pair in insertion order.
    #[getter]
    fn facts(&self, python: Python<'_>) -> PyResult<Vec<Py<PyCasFact>>> {
        self.0
            .facts()
            .into_iter()
            .map(|fact| PyCasFact::wrap(python, fact))
            .collect()
    }

    fn __len__(&self) -> usize {
        self.0.facts().len()
    }
}

/// Adapts an arbitrary Python object's `get(address)` method to `TrustedCas`.
struct PythonCasAdapter(Py<PyAny>);

impl TrustedCas for PythonCasAdapter {
    type Error = PyErr;

    fn get(&self, address: covalence_logic_cas::O256) -> Result<CasFact, Self::Error> {
        Python::attach(|python| {
            let address = PyO256::wrap(python, address)?;
            let returned = self.0.bind(python).call_method1("get", (address,))?;
            let fact = returned.extract::<PyRef<'_, PyCasFact>>()?;
            Ok(fact.0.clone())
        })
    }
}

/// Calls an arbitrary Python CAS and enforces that its fact answers `address`.
///
/// The object need only provide `get(O256) -> CasFact`. Its storage, network,
/// retry, and verification logic remains ordinary Python. Provider exceptions
/// propagate unchanged.
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3", name = "get_exact")]
fn get_exact_python(
    python: Python<'_>,
    provider: Py<PyAny>,
    address: PyRef<'_, PyO256>,
) -> PyResult<Py<PyCasFact>> {
    let requested = PyO256::value(&address);
    let adapter = PythonCasAdapter(provider);
    let fact = match get_exact(&adapter, requested) {
        Ok(fact) => fact,
        Err(GetError::Provider { source, .. }) => return Err(source),
        Err(GetError::WrongAddress {
            requested,
            returned,
        }) => {
            return Err(CasAddressMismatchError::new_err(format!(
                "CAS returned address {returned} for request {requested}"
            )));
        }
    };
    PyCasFact::wrap(python, fact)
}

/// Adds the whole-object CAS API to the extension module.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCasAssertion>()?;
    module.add_class::<PyCasFact>()?;
    module.add_class::<PyMemoryCas>()?;

    let python = module.py();
    for (name, exception) in [
        (
            "CasDigestMismatchError",
            PyType::new::<CasDigestMismatchError>(python),
        ),
        (
            "CasAddressMismatchError",
            PyType::new::<CasAddressMismatchError>(python),
        ),
        ("CasNotFoundError", PyType::new::<CasNotFoundError>(python)),
        (
            "CasCollisionError",
            PyType::new::<CasCollisionError>(python),
        ),
        (
            "CasAdmissionError",
            PyType::new::<CasAdmissionError>(python),
        ),
    ] {
        exception.setattr("__module__", "covalence.cas")?;
        module.add(name, exception)?;
    }

    let function = wrap_pyfunction!(get_exact_python, module)?;
    function.setattr("__module__", "covalence.cas")?;
    module.add_function(function)
}
