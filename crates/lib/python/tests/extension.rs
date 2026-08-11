//! A minimal extension module built only from `covalence-lib-python`.
//!
//! This is the crate's contract with its dependents: everything a binding crate
//! needs to define a module, take byte input, and raise an exception has to be
//! reachable without naming `PyO3` in a manifest. Nothing here imports `pyo3`
//! directly, so a gap in the re-export surface fails to compile.
//!
//! The module is registered with the interpreter this test binary embeds rather
//! than loaded from a shared object, which keeps the check inside `cargo test`
//! and Buck. Loading a real `.so` is what the Python suite in
//! `crates/ffi/python` does.

use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{append_to_inittab, types::PyBytes};

/// Length of any bytes-like argument.
//
// `Bytes` is taken by value because extraction produces an owned value; there
// is no borrowed form for `PyO3` to hand a function.
#[allow(clippy::needless_pass_by_value)]
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn byte_length(data: Bytes) -> usize {
    data.len()
}

/// Rejects its argument, to show how an error crosses the boundary.
#[pyfunction]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn always_invalid() -> PyResult<()> {
    Err(PyValueError::new_err("invalid by construction"))
}

#[pymodule]
#[pyo3(crate = "covalence_lib_python::pyo3")]
fn covalence_lib_python_test(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(byte_length, module)?)?;
    module.add_function(wrap_pyfunction!(always_invalid, module)?)
}

/// One test, because `append_to_inittab!` has to run before the interpreter
/// starts and any other test touching Python would start it first.
#[test]
fn a_module_built_from_the_re_exports_loads_and_runs() {
    append_to_inittab!(covalence_lib_python_test);

    Python::attach(|python| {
        let module = python
            .import("covalence_lib_python_test")
            .expect("the module registers");

        let length = |argument| -> PyResult<usize> {
            module
                .getattr("byte_length")?
                .call1((argument,))?
                .extract::<usize>()
        };

        assert_eq!(length(PyBytes::new(python, b"abc").into_any()).unwrap(), 3);

        let bytearray = python
            .eval(c"bytearray(b'abcd')", None, None)
            .expect("bytearray literal evaluates");
        assert_eq!(length(bytearray).unwrap(), 4);

        let memory = python
            .eval(c"memoryview(b'abcde')", None, None)
            .expect("memoryview literal evaluates");
        assert_eq!(length(memory).unwrap(), 5);

        let empty = python.eval(c"b''", None, None).expect("empty bytes");
        assert_eq!(length(empty).unwrap(), 0);

        // `str` is not bytes-like, and neither is an integer.
        for rejected in [c"'abc'", c"42", c"None"] {
            let argument = python.eval(rejected, None, None).expect("expression");
            let error = length(argument).expect_err("must be rejected");
            assert!(
                error.is_instance_of::<PyTypeError>(python),
                "{rejected:?} raised {error}"
            );
        }

        let error = module
            .getattr("always_invalid")
            .unwrap()
            .call0()
            .expect_err("must raise");
        assert!(error.is_instance_of::<PyValueError>(python));
        assert_eq!(error.value(python).to_string(), "invalid by construction");
    });
}
