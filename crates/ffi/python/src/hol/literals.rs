//! Literal composition at the Python boundary. All facts come from the kernel.

use covalence_data_num::{Int, Num};
use covalence_lib_python::prelude::*;
use covalence_lib_python::pyo3::{
    IntoPyObjectExt,
    types::{PyBool, PyBytes, PyDict, PyInt},
};
use covalence_logic_hol::{
    Ref, ThmId,
    literals::{
        BoolOp, Builtin, BytesOp, CastOp, Endian, EvalLimits, IntOp, LiteralType, LiteralValue,
        NatOp, WordOp, WordWidth,
    },
};

use super::{KernelId, PyKernel, PySequent, PyTm, value_error};

fn checked_term(kernel: &PyKernel, term: &PyTm) -> PyResult<Ref> {
    if term.owner != kernel.id {
        return Err(PyValueError::new_err("term belongs to another kernel"));
    }
    Ok(term.reference)
}

fn wrap(kernel: &PyKernel, reference: Ref) -> PyTm {
    PyTm {
        owner: kernel.id,
        reference,
    }
}

fn parse_type(name: &str) -> PyResult<LiteralType> {
    match name {
        "bool" => Ok(LiteralType::Bool),
        "i8" => Ok(LiteralType::I8),
        "i16" => Ok(LiteralType::I16),
        "i32" => Ok(LiteralType::I32),
        "i64" => Ok(LiteralType::I64),
        "nat" => Ok(LiteralType::Nat),
        "int" => Ok(LiteralType::Int),
        "bytes" => Ok(LiteralType::Bytes),
        _ => Err(PyValueError::new_err(format!(
            "unknown literal type {name}"
        ))),
    }
}

const fn type_name(ty: LiteralType) -> &'static str {
    match ty {
        LiteralType::Bool => "bool",
        LiteralType::I8 => "i8",
        LiteralType::I16 => "i16",
        LiteralType::I32 => "i32",
        LiteralType::I64 => "i64",
        LiteralType::Nat => "nat",
        LiteralType::Int => "int",
        LiteralType::Bytes => "bytes",
    }
}

fn python_int(value: &Bound<'_, PyAny>) -> PyResult<Int> {
    if value.is_instance_of::<PyBool>() {
        return Err(PyTypeError::new_err("expected an integer, excluding bool"));
    }
    let value = value.cast::<PyInt>()?;
    let bits: usize = value.call_method0("bit_length")?.extract()?;
    if bits / 8 + 1 > covalence_data_num::DEFAULT_MAX_BYTES {
        return Err(PyValueError::new_err(
            "integer literal exceeds the encoding limit",
        ));
    }
    let kwargs = PyDict::new(value.py());
    kwargs.set_item("signed", true)?;
    let encoded = value.call_method("to_bytes", (bits / 8 + 1, "big"), Some(&kwargs))?;
    let encoded = encoded.cast::<PyBytes>()?;
    let mut bytes = encoded.as_bytes();
    while bytes.len() > 1
        && ((bytes[0] == 0 && bytes[1] < 128) || (bytes[0] == 255 && bytes[1] >= 128))
    {
        bytes = &bytes[1..];
    }
    Int::from_canonical_bytes(bytes).map_err(value_error)
}

fn integer_to_python<'py>(
    python: Python<'py>,
    bytes: &[u8],
    signed: bool,
) -> PyResult<Bound<'py, PyAny>> {
    let kwargs = PyDict::new(python);
    kwargs.set_item("signed", signed)?;
    python.get_type::<PyInt>().call_method(
        "from_bytes",
        (PyBytes::new(python, bytes), "big"),
        Some(&kwargs),
    )
}

pub(super) fn literal(kernel: &mut PyKernel, ty: &str, value: &Bound<'_, PyAny>) -> PyResult<PyTm> {
    let ty = parse_type(ty)?;
    let value = match ty {
        LiteralType::Bool => LiteralValue::Bool(value.cast::<PyBool>()?.extract()?),
        LiteralType::Bytes => {
            LiteralValue::Bytes(value.cast::<PyBytes>()?.as_bytes().to_vec().into())
        }
        LiteralType::Nat => {
            LiteralValue::Nat(Num::try_from(python_int(value)?).map_err(value_error)?)
        }
        LiteralType::Int => LiteralValue::Int(python_int(value)?),
        LiteralType::I8 | LiteralType::I16 | LiteralType::I32 | LiteralType::I64 => {
            if value.is_instance_of::<PyBool>() {
                return Err(PyTypeError::new_err(
                    "expected integer bits, excluding bool",
                ));
            }
            let value = value.cast::<PyInt>()?;
            match ty {
                LiteralType::I8 => LiteralValue::I8(value.extract()?),
                LiteralType::I16 => LiteralValue::I16(value.extract()?),
                LiteralType::I32 => LiteralValue::I32(value.extract()?),
                LiteralType::I64 => LiteralValue::I64(value.extract()?),
                _ => unreachable!("fixed width selected"),
            }
        }
    };
    let reference = kernel.kernel.literal(value).map_err(value_error)?;
    Ok(wrap(kernel, reference))
}

pub(super) fn variable(kernel: &mut PyKernel, name: u64, ty: &str) -> PyResult<PyTm> {
    let ty = kernel
        .kernel
        .literal_ty(parse_type(ty)?)
        .map_err(value_error)?;
    let reference = kernel.kernel.tm_fv(name, ty).map_err(value_error)?;
    Ok(wrap(kernel, reference))
}

pub(super) fn term_type(kernel: &PyKernel, term: &PyTm) -> PyResult<&'static str> {
    let reference = checked_term(kernel, term)?;
    kernel
        .kernel
        .literal_type(reference)
        .map(type_name)
        .map_err(value_error)
}

pub(super) fn value<'py>(
    kernel: &PyKernel,
    python: Python<'py>,
    term: &PyTm,
) -> PyResult<Bound<'py, PyAny>> {
    let reference = checked_term(kernel, term)?;
    let value = kernel
        .kernel
        .arena()
        .literal_value(reference)
        .ok_or_else(|| PyValueError::new_err("term is not a literal"))?;
    match value {
        LiteralValue::Bool(value) => value.into_bound_py_any(python),
        LiteralValue::I8(value) => value.into_bound_py_any(python),
        LiteralValue::I16(value) => value.into_bound_py_any(python),
        LiteralValue::I32(value) => value.into_bound_py_any(python),
        LiteralValue::I64(value) => value.into_bound_py_any(python),
        LiteralValue::Bytes(value) => Ok(PyBytes::new(python, &value).into_any()),
        LiteralValue::Nat(value) => integer_to_python(python, &value.to_canonical_bytes(), false),
        LiteralValue::Int(value) => integer_to_python(python, &value.to_canonical_bytes(), true),
    }
}

fn width(name: &str) -> PyResult<WordWidth> {
    match name {
        "i8" => Ok(WordWidth::W8),
        "i16" => Ok(WordWidth::W16),
        "i32" => Ok(WordWidth::W32),
        "i64" => Ok(WordWidth::W64),
        _ => Err(PyValueError::new_err("expected i8, i16, i32, or i64")),
    }
}

fn endian(name: &str) -> PyResult<Endian> {
    match name {
        "little" => Ok(Endian::Little),
        "big" => Ok(Endian::Big),
        _ => Err(PyValueError::new_err("byte order must be little or big")),
    }
}

macro_rules! named {
    ($name:expr, $enum:ident, {$($text:literal => $variant:ident),* $(,)?}) => {
        match $name {
            $($text => Ok($enum::$variant),)*
            _ => Err(PyValueError::new_err(format!("unknown {} operation {}", stringify!($enum), $name))),
        }
    };
}

fn operation(name: &str) -> PyResult<Builtin> {
    let parts: Vec<_> = name.split('.').collect();
    match parts.as_slice() {
        ["bool", op] => named!(*op, BoolOp, {
            "not"=>Not,"and"=>And,"or"=>Or,"imp"=>Imp,"iff"=>Iff,"eq"=>Iff,
        })
        .map(Builtin::Bool),
        ["nat", op] => named!(*op, NatOp, {
            "add"=>Add,"sub"=>Sub,"mul"=>Mul,"div"=>Div,"rem"=>Rem,
            "succ"=>Succ,"pred"=>Pred,"pow"=>Pow,"eq"=>Eq,"ne"=>Ne,
            "lt"=>Lt,"le"=>Le,"gt"=>Gt,"ge"=>Ge,"min"=>Min,"max"=>Max,
            "and"=>And,"or"=>Or,"xor"=>Xor,"shl"=>Shl,"shr"=>Shr,
        })
        .map(Builtin::Nat),
        ["int", op] => named!(*op, IntOp, {
            "add"=>Add,"sub"=>Sub,"mul"=>Mul,"div"=>Div,"rem"=>Rem,
            "succ"=>Succ,"pred"=>Pred,"neg"=>Neg,"abs"=>Abs,"pow"=>Pow,
            "eq"=>Eq,"ne"=>Ne,"lt"=>Lt,"le"=>Le,"gt"=>Gt,"ge"=>Ge,
            "min"=>Min,"max"=>Max,"and"=>And,"or"=>Or,"xor"=>Xor,
            "not"=>Not,"shl"=>Shl,"shr"=>Shr,
        })
        .map(Builtin::Int),
        ["bytes", op] => named!(*op, BytesOp, {
            "empty"=>Empty,"singleton"=>Singleton,"cons"=>Cons,"snoc"=>Snoc,
            "append"=>Append,"repeat"=>Repeat,"len"=>Length,"eq"=>Eq,"ne"=>Ne,
            "lt"=>Lt,"le"=>Le,"gt"=>Gt,"ge"=>Ge,"get"=>Get,"set"=>Set,
            "slice"=>Slice,"replace"=>Replace,"take"=>Take,"drop"=>Drop,
        })
        .map(Builtin::Bytes),
        ["bytes", op, w, order] => {
            let (w, order) = (width(w)?, endian(order)?);
            Ok(Builtin::Bytes(match *op {
                "encode" => BytesOp::Encode(w, order),
                "decode" => BytesOp::Decode(w, order),
                "read" => BytesOp::Read(w, order),
                "write" => BytesOp::Write(w, order),
                _ => return Err(PyValueError::new_err("unknown byte codec operation")),
            }))
        }
        ["cast", "nat", "int"] => Ok(Builtin::Cast(CastOp::NatToInt)),
        ["cast", "int", "nat"] => Ok(Builtin::Cast(CastOp::IntToNat)),
        ["cast", w, "nat"] => Ok(Builtin::Cast(CastOp::WordToNat(width(w)?))),
        ["cast", w, "int", sign] => {
            let w = width(w)?;
            Ok(Builtin::Cast(match *sign {
                "signed" => CastOp::WordToIntS(w),
                "unsigned" => CastOp::WordToIntU(w),
                _ => return Err(PyValueError::new_err("expected signed or unsigned")),
            }))
        }
        ["cast", "nat", w, mode] => {
            let w = width(w)?;
            Ok(Builtin::Cast(match *mode {
                "checked" => CastOp::NatToWord(w),
                "wrap" => CastOp::NatToWordWrap(w),
                _ => return Err(PyValueError::new_err("expected checked or wrap")),
            }))
        }
        ["cast", "int", w, mode] => {
            let w = width(w)?;
            Ok(Builtin::Cast(match *mode {
                "signed" => CastOp::IntToWordS(w),
                "unsigned" => CastOp::IntToWordU(w),
                "wrap" => CastOp::IntToWordWrap(w),
                _ => return Err(PyValueError::new_err("expected signed, unsigned, or wrap")),
            }))
        }
        ["cast", a, b, mode] => {
            let (a, b) = (width(a)?, width(b)?);
            Ok(Builtin::Cast(match *mode {
                "wrap" => CastOp::WordWrap(a, b),
                "zero_extend" => CastOp::WordZeroExtend(a, b),
                "sign_extend" => CastOp::WordSignExtend(a, b),
                _ => {
                    return Err(PyValueError::new_err(
                        "expected wrap, zero_extend, or sign_extend",
                    ));
                }
            }))
        }
        [w, "extend_sign", from] => Ok(Builtin::Word(width(w)?, WordOp::ExtendSign(width(from)?))),
        [w, op] => {
            let w = width(w)?;
            named!(*op, WordOp, {
                "add"=>Add,"sub"=>Sub,"mul"=>Mul,"div_u"=>DivU,"div_s"=>DivS,
                "rem_u"=>RemU,"rem_s"=>RemS,"and"=>And,"or"=>Or,"xor"=>Xor,
                "not"=>Not,"shl"=>Shl,"shr_u"=>ShrU,"shr_s"=>ShrS,"rotl"=>Rotl,
                "rotr"=>Rotr,"clz"=>Clz,"ctz"=>Ctz,"popcnt"=>Popcnt,"eqz"=>Eqz,
                "eq"=>Eq,"ne"=>Ne,"lt_u"=>LtU,"le_u"=>LeU,"gt_u"=>GtU,"ge_u"=>GeU,
                "lt_s"=>LtS,"le_s"=>LeS,"gt_s"=>GtS,"ge_s"=>GeS,
            })
            .map(|op| Builtin::Word(w, op))
        }
        _ => Err(PyValueError::new_err(format!("unknown builtin {name}"))),
    }
}

pub(super) fn builtin(
    kernel: &mut PyKernel,
    name: &str,
    arguments: &[PyRef<'_, PyTm>],
) -> PyResult<PyTm> {
    let arguments = arguments
        .iter()
        .map(|term| checked_term(kernel, term))
        .collect::<PyResult<Vec<_>>>()?;
    if matches!(name, "bool.ne" | "bool.xor") {
        let mut staged = kernel.kernel.fork();
        let equality = staged
            .builtin(Builtin::Bool(BoolOp::Iff), &arguments)
            .map_err(value_error)?;
        let result = staged
            .builtin(Builtin::Bool(BoolOp::Not), &[equality])
            .map_err(value_error)?;
        kernel.kernel = staged;
        return Ok(wrap(kernel, result));
    }
    let operation = operation(name)?;
    let reference = kernel
        .kernel
        .builtin(operation, &arguments)
        .map_err(value_error)?;
    Ok(wrap(kernel, reference))
}

pub(super) fn function(
    kernel: &mut PyKernel,
    name: &str,
) -> PyResult<(PyTm, Vec<&'static str>, &'static str)> {
    let operation = operation(name)?;
    let (parameters, result) = operation.signature().map_err(value_error)?;
    let reference = kernel
        .kernel
        .builtin_const(operation)
        .map_err(value_error)?;
    Ok((
        wrap(kernel, reference),
        parameters.into_iter().map(type_name).collect(),
        type_name(result),
    ))
}

pub(super) fn apply(
    kernel: &mut PyKernel,
    function: &PyTm,
    arguments: &[PyRef<'_, PyTm>],
) -> PyResult<PyTm> {
    let mut reference = checked_term(kernel, function)?;
    let arguments = arguments
        .iter()
        .map(|term| checked_term(kernel, term))
        .collect::<PyResult<Vec<_>>>()?;
    let mut staged = kernel.kernel.fork();
    for argument in arguments {
        reference = staged.app(reference, argument).map_err(value_error)?;
    }
    kernel.kernel = staged;
    Ok(wrap(kernel, reference))
}

pub(super) fn match_function(
    kernel: &PyKernel,
    function: &PyTm,
    term: &PyTm,
) -> PyResult<Option<Vec<PyTm>>> {
    let function = checked_term(kernel, function)?;
    let term = checked_term(kernel, term)?;
    let arena = kernel.kernel.arena();
    let Some((expected, prefix)) = arena.builtin_application(function) else {
        return Err(PyValueError::new_err("expected a builtin function"));
    };
    let Some((actual, arguments)) = arena.builtin_application(term) else {
        return Ok(None);
    };
    let (parameters, _) = expected.signature().map_err(value_error)?;
    if actual != expected || arguments.len() != parameters.len() || !arguments.starts_with(&prefix)
    {
        return Ok(None);
    }
    Ok(Some(
        arguments[prefix.len()..]
            .iter()
            .map(|&argument| wrap(kernel, argument))
            .collect(),
    ))
}

/// A sealed record of the exact equality returned by checked reduction.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.literals",
    name = "HolLiteralReduction"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyLiteralReduction {
    owner: KernelId,
    source: Ref,
    result: Ref,
    theorem: ThmId,
    statement: PySequent,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyLiteralReduction {
    #[getter]
    fn source(&self) -> PyTm {
        PyTm {
            owner: self.owner,
            reference: self.source,
        }
    }
    #[getter]
    fn result(&self) -> PyTm {
        PyTm {
            owner: self.owner,
            reference: self.result,
        }
    }
    fn theorem(&self, kernel: &PyKernel) -> PyResult<i32> {
        if self.owner != kernel.id {
            return Err(PyValueError::new_err("evidence belongs to another kernel"));
        }
        let theorem = self.theorem.get();
        if kernel.theorem(theorem)? != self.statement {
            return Err(PyValueError::new_err(
                "theorem slot no longer contains this evidence",
            ));
        }
        Ok(theorem)
    }
}

pub(super) fn reduce(
    kernel: &mut PyKernel,
    term: &PyTm,
    max_bytes: usize,
    max_steps: u32,
) -> PyResult<PyLiteralReduction> {
    let source = checked_term(kernel, term)?;
    let (result, theorem) = kernel
        .kernel
        .reduce_builtin(
            source,
            EvalLimits {
                max_bytes,
                max_steps,
            },
        )
        .map_err(value_error)?;
    Ok(PyLiteralReduction {
        owner: kernel.id,
        source,
        result,
        theorem,
        statement: kernel.theorem(theorem.get())?,
    })
}
