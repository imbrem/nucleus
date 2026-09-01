//! Reference execution for supported WebAssembly language objects.
//!
//! This crate executes the owned representation from `covalence-lang-wasm`.
//! Its results are experimental data, not theorem facts. A future checked
//! acceleration boundary may choose an executor and thereby place that exact
//! path in the TCB; merely enabling or calling this crate grants no authority.

use covalence_lang_wasm::{
    InstructionKind, Limits, LoadError, Module, Profile, Value, ValueType, load,
};
use covalence_lib_error::snafu::{ResultExt, Snafu};

/// One externally visible execution event.
///
/// The first profile has no imports or other effects, so every successful v0
/// trace is empty. The enum is intentionally ready to grow with the supported
/// language profile.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Event {}

/// Why ordinary Wasm execution trapped.
///
/// No instruction in [`Profile::TinyCoreV0`] can currently produce a trap.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Trap {
    /// Execution reached an `unreachable` instruction.
    Unreachable,
}

/// Result of a finite execution attempt.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Outcome {
    /// The function returned these values in result order.
    Returned(Vec<Value>),
    /// The function produced a Wasm trap.
    Trapped(Trap),
    /// The supplied instruction budget was exhausted before termination.
    FuelExhausted,
}

/// Untrusted execution data returned by the reference evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExperimentalRun {
    /// Exact profile under which the module was recognized.
    pub profile: Profile,
    /// Export selected by the caller.
    pub entry: String,
    /// Raw input words supplied to the export.
    pub inputs: Vec<Value>,
    /// Externally visible events in execution order.
    pub trace: Vec<Event>,
    /// Return, trap, or resource outcome.
    pub outcome: Outcome,
    /// Number of decoded instructions executed.
    pub fuel_consumed: u64,
}

/// A malformed execution request or inconsistent owned Wasm object.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ExecError {
    /// The requested export is not the function selected by the tiny profile.
    #[snafu(display("unknown Wasm entry {requested:?}; available entry is {available:?}"))]
    UnknownEntry {
        /// Requested export name.
        requested: String,
        /// Sole available export name.
        available: String,
    },
    /// The argument count differs from the function type.
    #[snafu(display("Wasm entry expects {expected} arguments, found {actual}"))]
    ArgumentCount {
        /// Declared parameter count.
        expected: usize,
        /// Supplied value count.
        actual: usize,
    },
    /// A supplied value does not have the declared parameter type.
    #[snafu(display("Wasm argument {index} has the wrong value type"))]
    ArgumentType {
        /// Zero-based argument index.
        index: usize,
    },
    /// A local instruction refers outside the parameter and local array.
    #[snafu(display("Wasm local index {index} is outside {count} locals"))]
    LocalIndex {
        /// Rejected local index.
        index: u32,
        /// Total parameter and local count.
        count: usize,
    },
    /// An instruction requires more operand values than are present.
    #[snafu(display("Wasm instruction {instruction} underflowed the operand stack"))]
    StackUnderflow {
        /// Zero-based semantic instruction index.
        instruction: usize,
    },
    /// A return boundary found the wrong result stack shape.
    #[snafu(display("Wasm return expects {expected} results, found {actual}"))]
    ResultCount {
        /// Declared result count.
        expected: usize,
        /// Actual stack value count.
        actual: usize,
    },
    /// A return value does not have the declared result type.
    #[snafu(display("Wasm result {index} has the wrong value type"))]
    ResultType {
        /// Zero-based result index.
        index: usize,
    },
}

/// Failure to load exact bytes or execute the resulting owned module.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunBytesError {
    /// Binary loading or supported-profile extraction failed.
    #[snafu(display("could not load Wasm bytes: {source}"))]
    Load {
        /// Concrete language-layer rejection.
        source: LoadError,
    },
    /// Reference execution rejected the request or owned object.
    #[snafu(display("could not execute Wasm: {source}"))]
    Execute {
        /// Concrete evaluator rejection.
        source: ExecError,
    },
}

/// Loads and executes exact module bytes through the experimental path.
///
/// This convenience operation preserves the distinction between loading and
/// execution errors. It does not create checked evidence relating the input
/// bytes to the returned outcome.
///
/// # Errors
///
/// Returns [`RunBytesError::Load`] if the bytes are malformed, invalid,
/// unsupported, or exceed `limits`. Returns [`RunBytesError::Execute`] if the
/// entry, arguments, or extracted owned representation are inconsistent.
pub fn run_bytes(
    bytes: &[u8],
    profile: Profile,
    limits: Limits,
    entry: &str,
    inputs: &[Value],
    fuel: u64,
) -> Result<ExperimentalRun, RunBytesError> {
    let loaded = load(bytes, profile, limits).context(LoadSnafu)?;
    run(loaded.module(), entry, inputs, fuel).context(ExecuteSnafu)
}

/// Executes one supported owned module with an instruction budget.
///
/// Each semantic instruction consumes one unit of fuel. The final binary
/// `end` is structural and does not consume fuel. Fuel exhaustion is an
/// ordinary [`Outcome`], not an API error.
///
/// # Errors
///
/// Returns an error for an unknown export, arguments that disagree with the
/// function type, or an internally inconsistent [`Module`].
pub fn run(
    module: &Module,
    entry: &str,
    inputs: &[Value],
    fuel: u64,
) -> Result<ExperimentalRun, ExecError> {
    let function = module.function();
    if entry != function.export_name() {
        return Err(ExecError::UnknownEntry {
            requested: entry.to_owned(),
            available: function.export_name().to_owned(),
        });
    }
    if inputs.len() != function.params().len() {
        return Err(ExecError::ArgumentCount {
            expected: function.params().len(),
            actual: inputs.len(),
        });
    }
    for (index, (value, ty)) in inputs.iter().zip(function.params()).enumerate() {
        if !has_type(*value, *ty) {
            return Err(ExecError::ArgumentType { index });
        }
    }

    let mut locals = inputs.to_vec();
    locals.extend(function.locals().iter().copied().map(zero_of_type));
    let mut stack = Vec::new();
    let mut remaining = fuel;

    for (pc, instruction) in function.instructions().iter().enumerate() {
        if remaining == 0 {
            return Ok(experimental_run(
                module,
                entry,
                inputs,
                Outcome::FuelExhausted,
                fuel,
            ));
        }
        remaining -= 1;
        match instruction {
            InstructionKind::I32Const(bits) => stack.push(Value::I32(*bits)),
            InstructionKind::LocalGet(index) => {
                let value = locals
                    .get(*index as usize)
                    .copied()
                    .ok_or(ExecError::LocalIndex {
                        index: *index,
                        count: locals.len(),
                    })?;
                stack.push(value);
            }
            InstructionKind::I32Add => {
                let right = pop_i32(&mut stack, pc)?;
                let left = pop_i32(&mut stack, pc)?;
                stack.push(Value::I32(left.wrapping_add(right)));
            }
            InstructionKind::Return => {
                let results = return_results(&stack, function.results())?;
                return Ok(experimental_run(
                    module,
                    entry,
                    inputs,
                    Outcome::Returned(results),
                    fuel - remaining,
                ));
            }
        }
    }
    let results = end_results(&stack, function.results())?;
    Ok(experimental_run(
        module,
        entry,
        inputs,
        Outcome::Returned(results),
        fuel - remaining,
    ))
}

fn experimental_run(
    module: &Module,
    entry: &str,
    inputs: &[Value],
    outcome: Outcome,
    fuel_consumed: u64,
) -> ExperimentalRun {
    ExperimentalRun {
        profile: module.profile(),
        entry: entry.to_owned(),
        inputs: inputs.to_vec(),
        trace: Vec::new(),
        outcome,
        fuel_consumed,
    }
}

const fn has_type(value: Value, ty: ValueType) -> bool {
    matches!((value, ty), (Value::I32(_), ValueType::I32))
}

const fn zero_of_type(ty: ValueType) -> Value {
    match ty {
        ValueType::I32 => Value::I32(0),
    }
}

fn pop_i32(stack: &mut Vec<Value>, instruction: usize) -> Result<u32, ExecError> {
    match stack.pop() {
        Some(Value::I32(value)) => Ok(value),
        None => Err(ExecError::StackUnderflow { instruction }),
    }
}

fn end_results(stack: &[Value], types: &[ValueType]) -> Result<Vec<Value>, ExecError> {
    if stack.len() != types.len() {
        return Err(ExecError::ResultCount {
            expected: types.len(),
            actual: stack.len(),
        });
    }
    checked_results(stack, types)
}

fn return_results(stack: &[Value], types: &[ValueType]) -> Result<Vec<Value>, ExecError> {
    let start = stack
        .len()
        .checked_sub(types.len())
        .ok_or(ExecError::ResultCount {
            expected: types.len(),
            actual: stack.len(),
        })?;
    checked_results(&stack[start..], types)
}

fn checked_results(values: &[Value], types: &[ValueType]) -> Result<Vec<Value>, ExecError> {
    for (index, (value, ty)) in values.iter().zip(types).enumerate() {
        if !has_type(*value, *ty) {
            return Err(ExecError::ResultType { index });
        }
    }
    Ok(values.to_vec())
}
