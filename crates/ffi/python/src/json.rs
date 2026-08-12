//! `covalence-data-json` at the Python boundary.
//!
//! One class, `Json`: the `Arc`-backed immutable tree, behaving like the
//! usual pile of dicts and lists while enforcing what the stdlib `json`
//! module leaves to convention. Construction validates — string keys, finite
//! numbers, integers that fit 64 bits — and after that invalid states are
//! unrepresentable, so anything a `Json` holds serializes, always.
//!
//! Access unwraps leaves and wraps containers: `doc["port"]` is an `int`,
//! `doc["server"]` is another `Json` sharing the same tree. Extracting a
//! subtree is a reference-count bump, never a copy, which is the point of
//! wrapping the `Shared` family rather than converting to dicts at the
//! boundary.
//!
//! Equality converts the other operand, so `doc == {"a": 1}` compares
//! structurally. The exception is tuples: a tuple is hashable and would
//! compare equal to an array while hashing differently, and Python's
//! containers are allowed to assume `x == y` implies `hash(x) == hash(y)`.
//! For the same reason `__hash__` of a scalar delegates to the Python hash of
//! the value it unwraps to.
//!
//! One place equality is stricter than Python's: `1` and `1.0` are distinct
//! JSON numbers, as they are distinct JSON texts, so `Json(1) != 1.0` even
//! though `1 == 1.0`. Compare unwrapped values for Python's numeric
//! semantics.

// PyO3's calling convention, as in `hash.rs`: extraction produces owned
// values, and `#[pymethods]` borrow from the owning Python object.
#![allow(clippy::needless_pass_by_value, clippy::wrong_self_convention)]

use std::hash::{Hash, Hasher};

use covalence_data_json::Json;
use covalence_lib_python::exceptions::{PyIndexError, PyKeyError, create_exception};
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::types::{
    PyBool, PyDict, PyFloat, PyInt, PyIterator, PyList, PyString, PyTuple,
};

create_exception!(
    covalence,
    InvalidJsonError,
    PyValueError,
    "Text was not strict JSON: malformed, trailing input, or a duplicate object key."
);

/// How deep a Python structure may nest before conversion refuses.
///
/// Recursion on attacker-shaped input is a stack overflow, which `PyO3` cannot
/// turn into an exception the way it does a panic. The bound matches what
/// `serde_json` enforces when parsing, so text and objects admit the same
/// trees.
const MAX_DEPTH: usize = 128;

/// Converts a Python value into a [`Json`] tree, strictly.
fn convert(value: &Bound<'_, PyAny>) -> PyResult<Json> {
    convert_at(value, 0)
}

/// [`convert`], `depth` containers down.
///
/// `bool` is checked before `int` because it subclasses it, and an existing
/// [`PyJson`] splices in by cloning its `Arc` rather than by walking it —
/// which is also why splicing costs no depth: whatever it holds already fit.
fn convert_at(value: &Bound<'_, PyAny>, depth: usize) -> PyResult<Json> {
    if let Ok(json) = value.cast::<PyJson>() {
        return Ok(json.get().0.clone());
    }
    if depth >= MAX_DEPTH {
        return Err(PyValueError::new_err(format!(
            "value nests more than {MAX_DEPTH} levels deep"
        )));
    }
    if value.is_none() {
        return Ok(Json::Null);
    }
    if let Ok(flag) = value.cast::<PyBool>() {
        return Ok(Json::Bool(flag.is_true()));
    }
    if value.cast::<PyInt>().is_ok() {
        if let Ok(int) = value.extract::<i64>() {
            return Ok(Json::from(int));
        }
        if let Ok(int) = value.extract::<u64>() {
            return Ok(Json::from(int));
        }
        return Err(PyValueError::new_err(
            "integer does not fit in 64 bits, which strict JSON numbers require",
        ));
    }
    if value.cast::<PyFloat>().is_ok() {
        return Json::from_f64(value.extract::<f64>()?)
            .ok_or_else(|| PyValueError::new_err("non-finite floats are not JSON"));
    }
    if let Ok(text) = value.cast::<PyString>() {
        return Ok(Json::string(text.to_str()?));
    }
    if let Ok(list) = value.cast::<PyList>() {
        let values: PyResult<Vec<_>> = list.iter().map(|item| convert_at(&item, depth + 1)).collect();
        return Ok(Json::array(values?));
    }
    if let Ok(tuple) = value.cast::<PyTuple>() {
        let values: PyResult<Vec<_>> = tuple.iter().map(|item| convert_at(&item, depth + 1)).collect();
        return Ok(Json::array(values?));
    }
    if let Ok(dict) = value.cast::<PyDict>() {
        let mut pairs = Vec::with_capacity(dict.len());
        for (key, item) in dict {
            let Ok(key) = key.cast::<PyString>() else {
                return Err(PyTypeError::new_err(format!(
                    "JSON object keys must be str, not '{}'",
                    key.get_type().name()?
                )));
            };
            pairs.push((key.to_str()?.to_owned(), convert_at(&item, depth + 1)?));
        }
        // A dict cannot repeat a well-behaved key, but a str subclass with its
        // own equality can smuggle two spellings of one JSON key past it.
        return Json::object(pairs).map_err(|error| InvalidJsonError::new_err(error.to_string()));
    }
    Err(PyTypeError::new_err(format!(
        "cannot represent '{}' in JSON",
        value.get_type().name()?
    )))
}

/// Converts a [`Json`] tree to plain Python values, recursively.
fn unwrap<'py>(python: Python<'py>, value: &Json) -> PyResult<Bound<'py, PyAny>> {
    Ok(match value {
        Json::Null => python.None().into_bound(python),
        Json::Bool(value) => PyBool::new(python, *value).to_owned().into_any(),
        Json::Number(value) => {
            if let Some(int) = value.as_i64() {
                int.into_pyobject(python)?.into_any()
            } else if let Some(int) = value.as_u64() {
                int.into_pyobject(python)?.into_any()
            } else {
                value
                    .as_f64()
                    .expect("a JSON number is an integer or a float")
                    .into_pyobject(python)?
                    .into_any()
            }
        }
        Json::String(value) => PyString::new(python, value).into_any(),
        Json::Array(values) => {
            let list = PyList::empty(python);
            for value in values.iter() {
                list.append(unwrap(python, value)?)?;
            }
            list.into_any()
        }
        Json::Object(map) => {
            let dict = PyDict::new(python);
            for entry in map {
                dict.set_item(&*entry.key, unwrap(python, &entry.value)?)?;
            }
            dict.into_any()
        }
    })
}

/// What access returns: leaves unwrap to plain values, containers stay
/// wrapped so that nesting keeps sharing the tree.
fn item<'py>(python: Python<'py>, value: &Json) -> PyResult<Bound<'py, PyAny>> {
    match value {
        Json::Array(_) | Json::Object(_) => {
            Ok(Bound::new(python, PyJson(value.clone()))?.into_any())
        }
        leaf => unwrap(python, leaf),
    }
}

/// An immutable JSON document that acts like dicts and lists.
#[pyclass(frozen, module = "covalence.data.json", name = "Json")]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyJson(Json);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyJson {
    /// Validates `value` — dicts, lists, tuples, strs, ints, floats, bools,
    /// `None`, and `Json` itself — into an immutable document.
    #[new]
    fn new(value: &Bound<'_, PyAny>) -> PyResult<Self> {
        convert(value).map(Self)
    }

    /// Parses strict JSON text; a duplicate object key is an error.
    #[staticmethod]
    fn loads(python: Python<'_>, text: &str) -> PyResult<Self> {
        let text = text.to_owned();
        python
            .detach(|| covalence_data_json::from_str(&text))
            .map(Self)
            .map_err(|error| InvalidJsonError::new_err(error.to_string()))
    }

    /// Serializes: compact with sorted keys by default, indented when
    /// `pretty`.
    #[pyo3(signature = (*, pretty = false))]
    fn dumps(&self, python: Python<'_>, pretty: bool) -> String {
        let value = &self.0;
        python.detach(|| {
            if pretty {
                value.to_json_string_pretty()
            } else {
                value.to_json_string()
            }
        })
    }

    /// The plain-Python rendering: dicts, lists, strs, numbers, `None`.
    fn unwrap<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        unwrap(python, &self.0)
    }

    /// One of `"null"`, `"bool"`, `"number"`, `"string"`, `"array"`,
    /// `"object"`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.0.kind()
    }

    /// The value under `key` if this object has it, else `default`; a
    /// `TypeError` off an object, like the rest of the dict protocol here.
    #[pyo3(signature = (key, default = None))]
    fn get<'py>(
        &self,
        python: Python<'py>,
        key: &str,
        default: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let map = self
            .0
            .as_object()
            .ok_or_else(|| PyTypeError::new_err(format!("JSON {} has no get()", self.0.kind())))?;
        match map.get(key) {
            Some(value) => item(python, value),
            None => Ok(default.unwrap_or_else(|| python.None().into_bound(python))),
        }
    }

    /// An object's keys, in sorted order.
    fn keys(&self) -> PyResult<Vec<String>> {
        let map = self
            .0
            .as_object()
            .ok_or_else(|| PyTypeError::new_err(format!("JSON {} has no keys", self.0.kind())))?;
        Ok(map.keys().map(str::to_owned).collect())
    }

    /// An object's values, in key order.
    fn values<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        let map = self
            .0
            .as_object()
            .ok_or_else(|| PyTypeError::new_err(format!("JSON {} has no values", self.0.kind())))?;
        let list = PyList::empty(python);
        for value in map.values() {
            list.append(item(python, value)?)?;
        }
        Ok(list)
    }

    /// An object's `(key, value)` pairs, in key order.
    fn items<'py>(&self, python: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        let map = self
            .0
            .as_object()
            .ok_or_else(|| PyTypeError::new_err(format!("JSON {} has no items", self.0.kind())))?;
        let list = PyList::empty(python);
        for entry in map {
            list.append((&*entry.key, item(python, &entry.value)?))?;
        }
        Ok(list)
    }

    fn __len__(&self) -> PyResult<usize> {
        match &self.0 {
            Json::Array(values) => Ok(values.len()),
            Json::Object(map) => Ok(map.len()),
            other => Err(PyTypeError::new_err(format!(
                "JSON {} has no len()",
                other.kind()
            ))),
        }
    }

    fn __getitem__<'py>(
        &self,
        python: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        match &self.0 {
            Json::Object(map) => {
                let Ok(key) = key.cast::<PyString>() else {
                    return Err(PyTypeError::new_err(format!(
                        "JSON object keys are str, not '{}'",
                        key.get_type().name()?
                    )));
                };
                let key = key.to_str()?;
                match map.get(key) {
                    Some(value) => item(python, value),
                    None => Err(PyKeyError::new_err(key.to_owned())),
                }
            }
            Json::Array(values) => {
                let Ok(index) = key.extract::<isize>() else {
                    return Err(PyTypeError::new_err(format!(
                        "JSON array indices are int, not '{}'",
                        key.get_type().name()?
                    )));
                };
                let length = values.len();
                let resolved = if index < 0 {
                    index.checked_add_unsigned(length).filter(|at| *at >= 0)
                } else {
                    Some(index)
                };
                resolved
                    .and_then(|at| usize::try_from(at).ok())
                    .and_then(|at| values.get(at))
                    .map_or_else(
                        || Err(PyIndexError::new_err("JSON array index out of range")),
                        |value| item(python, value),
                    )
            }
            other => Err(PyTypeError::new_err(format!(
                "JSON {} is not subscriptable",
                other.kind()
            ))),
        }
    }

    fn __contains__(&self, needle: &Bound<'_, PyAny>) -> PyResult<bool> {
        match &self.0 {
            Json::Object(map) => Ok(needle
                .cast::<PyString>()
                .ok()
                .map(|key| key.to_str().map(|key| map.contains_key(key)))
                .transpose()?
                .unwrap_or(false)),
            Json::Array(values) => {
                Ok(convert(needle).is_ok_and(|needle| values.contains(&needle)))
            }
            other => Err(PyTypeError::new_err(format!(
                "JSON {} is not a container",
                other.kind()
            ))),
        }
    }

    /// Iterates keys for an object and elements for an array, like a dict and
    /// a list.
    fn __iter__<'py>(slf: &Bound<'py, Self>) -> PyResult<Bound<'py, PyIterator>> {
        let python = slf.py();
        let list = match &slf.get().0 {
            Json::Object(map) => {
                let keys = PyList::empty(python);
                for key in map.keys() {
                    keys.append(key)?;
                }
                keys
            }
            Json::Array(values) => {
                let elements = PyList::empty(python);
                for value in values.iter() {
                    elements.append(item(python, value)?)?;
                }
                elements
            }
            other => {
                return Err(PyTypeError::new_err(format!(
                    "JSON {} is not iterable",
                    other.kind()
                )));
            }
        };
        list.into_any().try_iter()
    }

    /// Structural equality, against another `Json` or anything that converts.
    ///
    /// A tuple is refused rather than converted: it would compare equal to an
    /// array while hashing differently, and Python containers may assume
    /// equal things hash alike.
    fn __eq__<'py>(&self, other: &Bound<'py, PyAny>, python: Python<'py>) -> Py<PyAny> {
        if other.cast::<PyTuple>().is_ok() {
            return python.NotImplemented();
        }
        match convert(other) {
            Ok(that) => PyBool::new(python, self.0 == that)
                .to_owned()
                .into_any()
                .unbind(),
            Err(_) => python.NotImplemented(),
        }
    }

    /// Agrees with `__eq__`: a scalar hashes as the value it unwraps to, and
    /// a container hashes structurally.
    fn __hash__(&self, python: Python<'_>) -> PyResult<isize> {
        match &self.0 {
            Json::Array(_) | Json::Object(_) => {
                let mut hasher = std::hash::DefaultHasher::new();
                self.0.hash(&mut hasher);
                // Wrapping is fine: a Python hash is an arbitrary isize.
                #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                Ok(hasher.finish() as isize)
            }
            leaf => unwrap(python, leaf)?.hash(),
        }
    }

    fn __bool__(&self) -> bool {
        match &self.0 {
            Json::Null => false,
            Json::Bool(value) => *value,
            Json::Number(value) => {
                if let Some(int) = value.as_i64() {
                    int != 0
                } else if let Some(int) = value.as_u64() {
                    int != 0
                } else {
                    value.as_f64().is_some_and(|float| float != 0.0)
                }
            }
            Json::String(value) => !value.is_empty(),
            Json::Array(values) => !values.is_empty(),
            Json::Object(map) => !map.is_empty(),
        }
    }

    fn __str__(&self) -> String {
        self.0.to_json_string()
    }

    fn __repr__(&self, python: Python<'_>) -> PyResult<String> {
        let text = PyString::new(python, &self.0.to_json_string());
        Ok(format!("Json.loads({})", text.repr()?))
    }
}

/// Adds the JSON API to the extension module.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyJson>()?;
    let exception = covalence_lib_python::pyo3::types::PyType::new::<InvalidJsonError>(module.py());
    exception.setattr("__module__", "covalence.data.json")?;
    module.add("InvalidJsonError", exception)
}
