//! Checked Alethe `QF_UF` replay at the Python boundary.

use covalence_lib_python::exceptions::create_exception;
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::PyType;
use covalence_logic_alethe::{Refutation, parse_cvc5_output, parse_smtlib2, replay_qf_uf};

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
#[pyclass(frozen, module = "covalence.logic.alethe", name = "QfUfRefutation")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
struct PyQfUfRefutation(Refutation);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyQfUfRefutation {
    /// One-based theorem index in the checked Ethane theorem arena.
    #[getter]
    fn theorem(&self) -> i32 {
        self.0.theorem().get()
    }

    /// Signed checked term indices forming the theorem's exact premise set.
    #[getter]
    fn assertions(&self) -> Vec<i32> {
        self.0
            .assertions()
            .iter()
            .map(|literal| literal.get())
            .collect()
    }

    /// Number of checked rows in the certificate's Ethane arena.
    #[getter]
    fn kernel_len(&self) -> usize {
        self.0.kernel().arena().len()
    }
}

#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn check_qf_uf(problem: &str, cvc5_output: &str) -> PyResult<PyQfUfRefutation> {
    let problem = parse_smtlib2(problem).map_err(rejection)?;
    let proof = parse_cvc5_output(cvc5_output).map_err(rejection)?;
    replay_qf_uf(&problem, &proof)
        .map(PyQfUfRefutation)
        .map_err(rejection)
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
