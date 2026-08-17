//! `covalence-data-cbor` at the Python boundary.

// PyO3 extracts owned Rust values for these Python arguments even though this
// thin boundary only reads them.
#![allow(clippy::needless_pass_by_value)]

use std::collections::HashSet;

use covalence_data_cbor::{Int, Value, ValueKind};
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    IntoPyObjectExt,
    basic::CompareOp,
    types::{PyBool, PyBytes, PyDict, PyInt, PyList, PyString, PyTuple, PyType},
};

/// An immutable, structurally shared CBOR value.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.data.cbor",
    name = "Cbor"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyCbor {
    value: Value,
}

impl PyCbor {
    fn wrap(value: Value) -> Self {
        Self { value }
    }

    fn allocated(python: Python<'_>, value: Value) -> PyResult<Py<Self>> {
        Py::new(python, Self::wrap(value))
    }
}

fn python_int(value: &Bound<'_, PyInt>) -> PyResult<Int> {
    let bits: usize = value.call_method0("bit_length")?.extract()?;
    let length = bits / 8 + 1;
    let kwargs = PyDict::new(value.py());
    kwargs.set_item("signed", true)?;
    let bytes = value.call_method("to_bytes", (length, "big"), Some(&kwargs))?;
    Int::from_canonical_bytes(bytes.cast::<PyBytes>()?.as_bytes())
        .map_err(|error| PyValueError::new_err(error.to_string()))
}

fn rust_int<'py>(python: Python<'py>, value: &Int) -> PyResult<Bound<'py, PyAny>> {
    python
        .get_type::<PyInt>()
        .call1((value.to_string(),))
        .map(Bound::into_any)
}

const MAX_CONTAINER_DEPTH: usize = 256;

fn from_python(
    value: &Bound<'_, PyAny>,
    ancestors: &mut HashSet<usize>,
    depth: usize,
) -> PyResult<Value> {
    if let Ok(value) = value.cast::<PyCbor>() {
        return Ok(value.get().value.clone());
    }
    if value.is_none() {
        return Ok(Value::null());
    }
    if let Ok(value) = value.cast::<PyBool>() {
        return Ok(Value::bool(value.extract()?));
    }
    if let Ok(value) = value.cast::<PyInt>() {
        return Ok(Value::integer(python_int(value)?));
    }
    if let Ok(value) = value.cast::<PyBytes>() {
        return Ok(Value::bytes(value.as_bytes()));
    }
    if let Ok(value) = value.cast::<PyString>() {
        return Ok(Value::text(value.to_str()?));
    }
    if depth == MAX_CONTAINER_DEPTH {
        return Err(PyValueError::new_err(format!(
            "CBOR input exceeds {MAX_CONTAINER_DEPTH} nested containers"
        )));
    }

    let identity = value.as_ptr() as usize;
    if let Ok(value) = value.cast::<PyList>() {
        if !ancestors.insert(identity) {
            return Err(PyValueError::new_err("CBOR input contains a cycle"));
        }
        let result = value
            .iter()
            .map(|value| from_python(&value, ancestors, depth + 1))
            .collect::<PyResult<Vec<_>>>();
        ancestors.remove(&identity);
        return result.map(Value::array);
    }
    if let Ok(value) = value.cast::<PyDict>() {
        if !ancestors.insert(identity) {
            return Err(PyValueError::new_err("CBOR input contains a cycle"));
        }
        let result = value
            .iter()
            .map(|(key, value)| {
                Ok((
                    from_python(&key, ancestors, depth + 1)?,
                    from_python(&value, ancestors, depth + 1)?,
                ))
            })
            .collect::<PyResult<Vec<_>>>();
        ancestors.remove(&identity);
        return result.map(Value::map);
    }

    Err(PyTypeError::new_err(format!(
        "cannot construct CBOR from {}",
        value.get_type().name()?
    )))
}

fn converted(value: &Bound<'_, PyAny>) -> PyResult<Value> {
    from_python(value, &mut HashSet::new(), 0)
}

fn equals_python(value: &Value, other: &Bound<'_, PyAny>) -> PyResult<Option<bool>> {
    if let Ok(other) = other.cast::<PyCbor>() {
        return Ok(Some(value == &other.get().value));
    }
    match value.kind() {
        ValueKind::Integer(value) => {
            if other.is_instance_of::<PyBool>() || !other.is_instance_of::<PyInt>() {
                return Ok(None);
            }
            Ok(Some(value == &python_int(other.cast::<PyInt>()?)?))
        }
        ValueKind::Bytes(value) => Ok(other
            .cast::<PyBytes>()
            .ok()
            .map(|other| value.as_ref() == other.as_bytes())),
        ValueKind::Text(value) => Ok(other
            .cast::<PyString>()
            .ok()
            .map(|other| other.to_str().is_ok_and(|other| value.as_ref() == other))),
        ValueKind::Simple(expected @ (20 | 21)) => {
            let Ok(other) = other.cast::<PyBool>() else {
                return Ok(None);
            };
            Ok(Some(other.extract::<bool>()? == (*expected == 21)))
        }
        ValueKind::Simple(22) if other.is_none() => Ok(Some(true)),
        ValueKind::Array(values) => {
            let Ok(other) = other.cast::<PyList>() else {
                return Ok(None);
            };
            if values.len() != other.len() {
                return Ok(Some(false));
            }
            for (value, other) in values.iter().zip(other.iter()) {
                if !equals_python(value, &other)?.unwrap_or(false) {
                    return Ok(Some(false));
                }
            }
            Ok(Some(true))
        }
        ValueKind::Map(entries) => {
            let Ok(other) = other.cast::<PyDict>() else {
                return Ok(None);
            };
            if entries.len() != other.len() {
                return Ok(Some(false));
            }
            for ((key, value), (other_key, other_value)) in entries.iter().zip(other.iter()) {
                if !equals_python(key, &other_key)?.unwrap_or(false)
                    || !equals_python(value, &other_value)?.unwrap_or(false)
                {
                    return Ok(Some(false));
                }
            }
            Ok(Some(true))
        }
        ValueKind::Simple(_)
        | ValueKind::Float16(_)
        | ValueKind::Float32(_)
        | ValueKind::Float64(_)
        | ValueKind::Tag(_, _) => Ok(None),
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCbor {
    #[new]
    fn new(value: &Bound<'_, PyAny>) -> PyResult<Self> {
        Ok(Self::wrap(converted(value)?))
    }

    #[staticmethod]
    fn from_python(value: &Bound<'_, PyAny>) -> PyResult<Self> {
        Self::new(value)
    }

    #[staticmethod]
    fn integer(value: &Bound<'_, PyInt>) -> PyResult<Self> {
        Ok(Self::wrap(Value::integer(python_int(value)?)))
    }

    #[staticmethod]
    fn bytes(value: Bytes) -> Self {
        Self::wrap(Value::bytes(value.as_slice()))
    }

    #[staticmethod]
    fn text(value: &str) -> Self {
        Self::wrap(Value::text(value))
    }

    #[staticmethod]
    fn simple(value: u8) -> Self {
        Self::wrap(Value::simple(value))
    }

    #[staticmethod]
    fn bool(value: bool) -> Self {
        Self::wrap(Value::bool(value))
    }

    #[staticmethod]
    fn null() -> Self {
        Self::wrap(Value::null())
    }

    #[staticmethod]
    fn undefined() -> Self {
        Self::wrap(Value::undefined())
    }

    #[staticmethod]
    fn float16(bits: u16) -> Self {
        Self::wrap(Value::float16(bits))
    }

    #[staticmethod]
    fn float32(bits: u32) -> Self {
        Self::wrap(Value::float32(bits))
    }

    #[staticmethod]
    fn float64(bits: u64) -> Self {
        Self::wrap(Value::float64(bits))
    }

    #[staticmethod]
    fn tag(tag: u64, value: PyRef<'_, Self>) -> Self {
        Self::wrap(Value::tag(tag, value.value.clone()))
    }

    #[staticmethod]
    fn array(python: Python<'_>, values: Vec<Py<Self>>) -> Self {
        Self::wrap(Value::array(
            values
                .iter()
                .map(|value| value.borrow(python).value.clone())
                .collect::<Vec<_>>(),
        ))
    }

    #[staticmethod]
    fn map(python: Python<'_>, entries: Vec<(Py<Self>, Py<Self>)>) -> Self {
        Self::wrap(Value::map(
            entries
                .iter()
                .map(|(key, value)| {
                    (
                        key.borrow(python).value.clone(),
                        value.borrow(python).value.clone(),
                    )
                })
                .collect::<Vec<_>>(),
        ))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.value.kind() {
            ValueKind::Integer(_) => "integer",
            ValueKind::Bytes(_) => "bytes",
            ValueKind::Text(_) => "text",
            ValueKind::Simple(_) => "simple",
            ValueKind::Float16(_) => "float16",
            ValueKind::Float32(_) => "float32",
            ValueKind::Float64(_) => "float64",
            ValueKind::Tag(_, _) => "tag",
            ValueKind::Array(_) => "array",
            ValueKind::Map(_) => "map",
        }
    }

    #[getter]
    fn value(&self, python: Python<'_>) -> PyResult<Py<PyAny>> {
        match self.value.kind() {
            ValueKind::Integer(value) => Ok(rust_int(python, value)?.unbind()),
            ValueKind::Bytes(value) => Ok(PyBytes::new(python, value).into_any().unbind()),
            ValueKind::Text(value) => value.as_ref().into_py_any(python),
            ValueKind::Simple(value) => value.into_py_any(python),
            ValueKind::Float16(bits) => bits.into_py_any(python),
            ValueKind::Float32(bits) => bits.into_py_any(python),
            ValueKind::Float64(bits) => bits.into_py_any(python),
            ValueKind::Tag(tag, value) => PyTuple::new(
                python,
                [
                    tag.into_py_any(python)?,
                    Self::allocated(python, value.clone())?.into_any(),
                ],
            )
            .map(|value| value.into_any().unbind()),
            ValueKind::Array(values) => {
                let values = values
                    .iter()
                    .map(|value| Self::allocated(python, value.clone()))
                    .collect::<PyResult<Vec<_>>>()?;
                Ok(PyTuple::new(python, values)?.into_any().unbind())
            }
            ValueKind::Map(entries) => {
                let entries = entries
                    .iter()
                    .map(|(key, value)| {
                        PyTuple::new(
                            python,
                            [
                                Self::allocated(python, key.clone())?,
                                Self::allocated(python, value.clone())?,
                            ],
                        )
                    })
                    .collect::<PyResult<Vec<_>>>()?;
                Ok(PyTuple::new(python, entries)?.into_any().unbind())
            }
        }
    }

    fn __repr__(&self) -> String {
        format!("Cbor(kind='{}')", self.kind())
    }

    fn __richcmp__(
        &self,
        other: &Bound<'_, PyAny>,
        op: CompareOp,
        python: Python<'_>,
    ) -> PyResult<Py<PyAny>> {
        match op {
            CompareOp::Eq => {
                let Some(equal) = equals_python(&self.value, other)? else {
                    return Ok(python.NotImplemented());
                };
                equal.into_py_any(python)
            }
            CompareOp::Ne => {
                let Some(equal) = equals_python(&self.value, other)? else {
                    return Ok(python.NotImplemented());
                };
                (!equal).into_py_any(python)
            }
            _ => Ok(python.NotImplemented()),
        }
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCbor>()?;
    PyType::new::<PyCbor>(module.py()).setattr("__hash__", module.py().None())
}
