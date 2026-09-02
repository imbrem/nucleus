//! Small compositional semantic schemas and checked route agreement.
//!
//! A [`Program`] is ordinary untrusted data. Its evaluator is generic over the
//! value and instruction-operation types, so a schema can be interpreted into
//! HOL terms, an executable model, or an audit trace without changing the
//! program representation. The checked add package below uses the same
//! parameter-only instruction data for Route B while Route A constructs its
//! result directly.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynRel, ThmId};

/// An ordered program over an arbitrary instruction schema.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program<Instruction> {
    instructions: Vec<Instruction>,
}

impl<Instruction> Program<Instruction> {
    /// Composes a program from its instruction sequence.
    #[must_use]
    pub const fn new(instructions: Vec<Instruction>) -> Self {
        Self { instructions }
    }

    /// Borrows instructions in execution order.
    #[must_use]
    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }

    /// Decomposes the program without cloning its instructions.
    #[must_use]
    pub fn into_instructions(self) -> Vec<Instruction> {
        self.instructions
    }
}

/// Parameter-only stack instructions over an arbitrary binary-operation tag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParameterInstruction<Operation> {
    /// Pushes one function parameter by zero-based index.
    LocalGet(u32),
    /// Pops right then left and pushes the binary result.
    Binary(Operation),
    /// Returns the sole stack value.
    Return,
}

/// Why generic parameter-program evaluation failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationError {
    /// An operation needed more stack operands than were present.
    StackUnderflow,
    /// Return did not observe exactly one result.
    WrongResultCount,
    /// Execution reached the end without a return instruction.
    MissingReturn,
}

impl<Operation: Copy> Program<ParameterInstruction<Operation>> {
    /// Interprets this program with caller-supplied local and binary semantics.
    ///
    /// # Errors
    ///
    /// Returns a callback error, stack underflow, a non-singleton return
    /// stack, or a program that reaches its end without returning.
    pub fn evaluate<Value, Error>(
        &self,
        mut local: impl FnMut(u32) -> Result<Value, Error>,
        mut binary: impl FnMut(Operation, Value, Value) -> Result<Value, Error>,
    ) -> Result<Value, ProgramError<Error>> {
        let mut stack = Vec::new();
        for instruction in &self.instructions {
            match *instruction {
                ParameterInstruction::LocalGet(index) => {
                    stack.push(local(index).map_err(ProgramError::Callback)?);
                }
                ParameterInstruction::Binary(operation) => {
                    let right = stack
                        .pop()
                        .ok_or(ProgramError::Evaluation(EvaluationError::StackUnderflow))?;
                    let left = stack
                        .pop()
                        .ok_or(ProgramError::Evaluation(EvaluationError::StackUnderflow))?;
                    stack.push(binary(operation, left, right).map_err(ProgramError::Callback)?);
                }
                ParameterInstruction::Return => {
                    if stack.len() != 1 {
                        return Err(ProgramError::Evaluation(EvaluationError::WrongResultCount));
                    }
                    return stack
                        .pop()
                        .ok_or(ProgramError::Evaluation(EvaluationError::WrongResultCount));
                }
            }
        }
        Err(ProgramError::Evaluation(EvaluationError::MissingReturn))
    }
}

/// Error from a generic program evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramError<Error> {
    /// A caller-supplied semantic operation failed.
    Callback(Error),
    /// The instruction sequence was not a valid returning stack program.
    Evaluation(EvaluationError),
}

/// Binary-operation tags in the first parameter-only add schema.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AddOperation {
    /// WebAssembly `i32.add`.
    I32Add,
}

/// The exact program schema used by the first two-route theorem.
#[must_use]
pub fn parameter_add_program() -> Program<ParameterInstruction<AddOperation>> {
    Program::new(vec![
        ParameterInstruction::LocalGet(0),
        ParameterInstruction::LocalGet(1),
        ParameterInstruction::Binary(AddOperation::I32Add),
        ParameterInstruction::Return,
    ])
}

/// Checked roots witnessing agreement of direct and interpreted add routes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AddRouteAgreement {
    /// Route A: direct application of the supplied addition operation.
    pub direct: Ref,
    /// Route B: result of interpreting [`parameter_add_program`].
    pub interpreted: Ref,
    /// Object-language equality between the two route results.
    pub proposition: Ref,
    /// Premise-free checked theorem concluding [`Self::proposition`].
    pub theorem: ThmId,
}

/// Why the checked add-route package could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AddSemanticsError {
    /// The fixed program unexpectedly failed its stack discipline.
    #[snafu(display("parameter-add program is invalid: {failure:?}"))]
    Program {
        /// Generic stack-machine failure.
        failure: EvaluationError,
    },
    /// The fixed program requested a parameter outside its two-input schema.
    #[snafu(display("parameter-add program requested unexpected local {index}"))]
    UnexpectedLocal {
        /// Unsupported zero-based local index.
        index: u32,
    },
    /// A public checked HOL operation rejected the construction or proof.
    #[snafu(display("checked parameter-add semantics failed: {source}"))]
    Kernel {
        /// Underlying kernel rejection.
        source: KernelError,
    },
}

/// Constructs both add routes and proves their equality through checked HOL.
///
/// `word_ty` is deliberately abstract, and `add` supplies all arithmetic
/// meaning. This theorem therefore assumes no concrete integer model. Route A
/// constructs `add left right` directly. Route B interprets the generic
/// instruction data returned by [`parameter_add_program`]. The frontend only
/// supplies syntactic congruence evidence; equality reflexivity and theorem
/// conversion remain checked kernel operations.
///
/// # Errors
///
/// Returns an error if the inputs are ill-kinded or ill-typed, program
/// interpretation fails, or any checked syntax/equality/theorem rule rejects
/// the agreement proof. The kernel is unchanged on failure.
pub fn prove_parameter_add_agreement(
    kernel: &mut Kernel,
    bool_ty: Ref,
    word_ty: Ref,
    add: Ref,
    left: Ref,
    right: Ref,
) -> Result<AddRouteAgreement, AddSemanticsError> {
    let mut staged = kernel.fork();

    // Route A is authored directly from the selected semantic operation.
    let direct_partial = staged
        .app(add, left)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let direct = staged
        .app(direct_partial, right)
        .map_err(|source| AddSemanticsError::Kernel { source })?;

    // Route B consumes the instruction schema as data through the generic
    // evaluator.
    let (interpreted_partial, interpreted) =
        interpret_parameter_add(&mut staged, add, left, right)?;

    let add_same = staged
        .syn_refl(None, SynRel::Syn, add)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let left_same = staged
        .syn_refl(None, SynRel::Syn, left)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let partial_same = staged
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            direct_partial,
            interpreted_partial,
            &[add_same, left_same],
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let right_same = staged
        .syn_refl(None, SynRel::Syn, right)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let result_same = staged
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            direct,
            interpreted,
            &[partial_same, right_same],
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    staged
        .union_syn_fact(result_same)
        .map_err(|source| AddSemanticsError::Kernel { source })?;

    let reflexive = staged
        .refl(bool_ty, direct)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let proposition = staged
        .eq_at(bool_ty, word_ty, direct, interpreted)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let word_same = staged
        .syn_refl(None, SynRel::Syn, word_ty)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let direct_same = staged
        .syn_refl(None, SynRel::Syn, direct)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let proposition_same = staged
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            reflexive.equality,
            proposition,
            &[word_same, direct_same, result_same],
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    staged
        .union_syn_fact(proposition_same)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    staged
        .convert_theorem(reflexive.theorem, reflexive.equality, proposition)
        .map_err(|source| AddSemanticsError::Kernel { source })?;

    *kernel = staged;
    Ok(AddRouteAgreement {
        direct,
        interpreted,
        proposition,
        theorem: reflexive.theorem,
    })
}

fn interpret_parameter_add(
    kernel: &mut Kernel,
    add: Ref,
    left: Ref,
    right: Ref,
) -> Result<(Ref, Ref), AddSemanticsError> {
    let mut partial = None;
    let result = parameter_add_program()
        .evaluate(
            |index| match index {
                0 => Ok(left),
                1 => Ok(right),
                _ => Err(AddSemanticsError::UnexpectedLocal { index }),
            },
            |operation, lhs, rhs| match operation {
                AddOperation::I32Add => {
                    let application = kernel
                        .app(add, lhs)
                        .map_err(|source| AddSemanticsError::Kernel { source })?;
                    partial = Some(application);
                    kernel
                        .app(application, rhs)
                        .map_err(|source| AddSemanticsError::Kernel { source })
                }
            },
        )
        .map_err(|failure| match failure {
            ProgramError::Callback(failure) => failure,
            ProgramError::Evaluation(failure) => AddSemanticsError::Program { failure },
        })?;
    let partial = partial.ok_or(AddSemanticsError::Program {
        failure: EvaluationError::StackUnderflow,
    })?;
    Ok((partial, result))
}
