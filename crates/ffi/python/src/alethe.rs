//! Checked Alethe `QF_UF` replay at the Python boundary.

use std::sync::OnceLock;

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_alethe::{Refutation, parse_cvc5_output, parse_smtlib2, replay_qf_uf};

use crate::hol::{KernelId, PyKernel};

create_exception!(
    covalence,
    AletheError,
    PyValueError,
    "An Alethe problem or proof was rejected."
);

fn rejection(error: impl std::fmt::Display) -> PyErr {
    AletheError::new_err(error.to_string())
}

/// An exact, kernel-checked `assertions |- false` `QF_UF` certificate.
///
/// The exported indices address the private Ethane arena the replay built,
/// not any kernel the caller already holds. `kernel` hands that arena to
/// Python, and the guarded accessors reject an index read against a kernel
/// of another identity.
#[pyclass(frozen, module = "covalence.logic.alethe", name = "QfUfRefutation")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
struct PyQfUfRefutation {
    refutation: Refutation,
    owner: KernelId,
    handle: OnceLock<Py<PyKernel>>,
}

impl PyQfUfRefutation {
    fn new(refutation: Refutation) -> Self {
        Self {
            refutation,
            owner: KernelId::fresh(),
            handle: OnceLock::new(),
        }
    }

    fn checked_owner(&self, kernel: &PyKernel) -> PyResult<()> {
        if kernel.id() == self.owner {
            return Ok(());
        }
        Err(AletheError::new_err(
            "refutation indices belong to a different kernel",
        ))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyQfUfRefutation {
    /// One-based theorem index in the certificate's own Ethane arena.
    #[getter]
    fn theorem(&self) -> i32 {
        self.refutation.theorem().get()
    }

    /// Signed checked term indices forming the theorem's exact premise set.
    #[getter]
    fn assertions(&self) -> Vec<i32> {
        self.refutation
            .assertions()
            .iter()
            .map(|literal| literal.get())
            .collect()
    }

    /// Number of checked rows in the certificate's Ethane arena.
    #[getter]
    fn kernel_len(&self) -> usize {
        self.refutation.kernel().arena().len()
    }

    /// Returns the checked kernel the exported indices address.
    ///
    /// The same kernel object comes back every time, so it is the one kernel
    /// carrying this certificate's identity. A kernel only ever grows through
    /// checked rules, so the theorem and assertion indices stay valid however
    /// the caller extends it.
    fn kernel(&self, python: Python<'_>) -> PyResult<Py<PyKernel>> {
        if let Some(kernel) = self.handle.get() {
            return Ok(kernel.clone_ref(python));
        }
        let kernel = Py::new(
            python,
            PyKernel::adopt(self.refutation.kernel().fork(), self.owner),
        )?;
        Ok(self.handle.get_or_init(|| kernel).clone_ref(python))
    }

    /// Returns the theorem index, rejecting a kernel it does not index.
    fn theorem_in(&self, kernel: &Bound<'_, PyKernel>) -> PyResult<i32> {
        let kernel = kernel.try_borrow()?;
        self.checked_owner(&kernel)?;
        Ok(self.theorem())
    }

    /// Returns the assertion indices, rejecting a kernel they do not index.
    fn assertions_in(&self, kernel: &Bound<'_, PyKernel>) -> PyResult<Vec<i32>> {
        let kernel = kernel.try_borrow()?;
        self.checked_owner(&kernel)?;
        Ok(self.assertions())
    }
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn check_qf_uf(python: Python<'_>, problem: &str, cvc5_output: &str) -> PyResult<PyQfUfRefutation> {
    // Parsing and replay are pure Rust that touches no Python object, so the
    // interpreter is detached for the duration and other threads keep running.
    // The rejection is built inside the closure because `new_err` is lazy and
    // needs no interpreter.
    python.detach(|| {
        let problem = parse_smtlib2(problem).map_err(rejection)?;
        let proof = parse_cvc5_output(cvc5_output).map_err(rejection)?;
        replay_qf_uf(&problem, &proof)
            .map(PyQfUfRefutation::new)
            .map_err(rejection)
    })
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyQfUfRefutation>()?;
    let function = wrap_pyfunction!(check_qf_uf, module)?;
    function.setattr("__module__", "covalence.logic.alethe")?;
    module.add_function(function)?;
    let error = PyType::new::<AletheError>(module.py());
    error.setattr("__module__", "covalence.logic.alethe")?;
    module.add("AletheError", error)
}
