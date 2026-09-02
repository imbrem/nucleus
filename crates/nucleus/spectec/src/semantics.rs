//! Small compositional semantic schemas and checked route agreement.
//!
//! A [`Program`] is ordinary untrusted data. Its evaluator is generic over the
//! value and instruction-operation types, so a schema can be interpreted into
//! HOL terms, an executable model, or an audit trace without changing the
//! program representation. The checked add package below uses the same
//! parameter-only instruction data for Route B while Route A constructs its
//! result directly.

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, SynRel, ThmId, wire};
use covalence_logic_hol_derived::{ModelError, SyntaxError, join_same_syntax, substitute};

use crate::{AddSliceArtifact, AddSliceError, AddSlicePlan, Source};

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
    /// Route B's selected program represented as resident HOL data.
    pub program: Ref,
    /// Route A: direct application of the supplied addition operation.
    pub direct: Ref,
    /// Route B: result of interpreting [`parameter_add_program`].
    pub interpreted: Ref,
    /// Object-language equality between the two route results.
    pub proposition: Ref,
    /// Premise-free checked theorem concluding [`Self::proposition`].
    pub theorem: ThmId,
}

/// Source-derived add plan, executable schema, and checked route theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddSliceAgreement {
    plan: AddSlicePlan,
    program: Program<ParameterInstruction<AddOperation>>,
    checked: AddRouteAgreement,
    cids: PipelineCids,
}

impl AddSliceAgreement {
    /// Returns the exhaustive source coverage used by both routes.
    #[must_use]
    pub const fn plan(&self) -> &AddSlicePlan {
        &self.plan
    }

    /// Returns the executable instruction data consumed by Route B.
    #[must_use]
    pub const fn program(&self) -> &Program<ParameterInstruction<AddOperation>> {
        &self.program
    }

    /// Returns the checked route roots and agreement theorem.
    #[must_use]
    pub const fn checked(&self) -> AddRouteAgreement {
        self.checked
    }

    /// Returns exact input, init, translation, and output content links.
    #[must_use]
    pub const fn cids(&self) -> PipelineCids {
        self.cids
    }
}

/// Generic content links for one deterministic translation pipeline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PipelineCids {
    input: Cid,
    init: Cid,
    translation: Cid,
    output: Cid,
}

impl PipelineCids {
    /// Composes the four exact pipeline links.
    #[must_use]
    pub const fn new(input: Cid, init: Cid, translation: Cid, output: Cid) -> Self {
        Self {
            input,
            init,
            translation,
            output,
        }
    }

    /// Returns the exact input artifact link.
    #[must_use]
    pub const fn input(self) -> Cid {
        self.input
    }

    /// Returns the initial checked-state link.
    #[must_use]
    pub const fn init(self) -> Cid {
        self.init
    }

    /// Returns the translation-policy artifact link.
    #[must_use]
    pub const fn translation(self) -> Cid {
        self.translation
    }

    /// Returns the final checked-state link.
    #[must_use]
    pub const fn output(self) -> Cid {
        self.output
    }
}

/// Why the checked add-route package could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AddSemanticsError {
    /// The program is outside the one exact instruction sequence supported by
    /// this first semantic package.
    #[snafu(display("unsupported parameter-add instruction sequence"))]
    UnsupportedProgram,
    /// A public checked HOL operation rejected the construction or proof.
    #[snafu(display("checked parameter-add semantics failed: {source}"))]
    Kernel {
        /// Underlying kernel rejection.
        source: KernelError,
    },
    /// Checked application congruence failed during one evaluator stage.
    #[snafu(display("checked {stage} evaluator congruence failed: {source}"))]
    BetaCongruence {
        /// Evaluator application stage.
        stage: &'static str,
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Untrusted substitution orchestration could not produce checked beta
    /// evidence.
    #[snafu(display("could not reduce internal parameter-add data: {source}"))]
    Substitution {
        /// Derived substitution failure.
        source: ModelError,
    },
    /// Untrusted same-syntax traversal could not construct checked evidence.
    #[snafu(display("could not relate internal parameter-add results: {source}"))]
    Syntax {
        /// Derived syntax-certificate failure.
        source: SyntaxError,
    },
}

/// Why a source-derived add agreement package could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AddSliceAgreementError {
    /// The source did not match the closed add-slice coverage and body shapes.
    #[snafu(display("could not derive parameter-add coverage: {source}"))]
    Plan {
        /// Structural coverage failure.
        source: AddSliceError,
    },
    /// Public checked HOL operations rejected the two-route construction.
    #[snafu(display("could not prove parameter-add route agreement: {source}"))]
    Semantics {
        /// Checked semantic construction failure.
        source: AddSemanticsError,
    },
    /// Canonical checked-kernel encoding failed.
    #[snafu(display("could not encode {stage} parameter-add kernel: {source}"))]
    KernelEncode {
        /// Pipeline stage being addressed.
        stage: &'static str,
        /// Canonical arena encoding failure.
        source: wire::EncodeError,
    },
}

/// Derives the closed add slice and checks both semantic routes in one step.
///
/// # Errors
///
/// Returns an error if exhaustive source coverage or selected rule-body shape
/// validation fails, or if [`prove_add_program_agreement`] rejects the checked
/// construction. The kernel is unchanged on any failure.
pub fn prove_add_slice_agreement(
    source: &Source,
    kernel: &mut Kernel,
    bool_ty: Ref,
    word_ty: Ref,
    add: Ref,
    left: Ref,
    right: Ref,
) -> Result<AddSliceAgreement, AddSliceAgreementError> {
    let plan =
        AddSlicePlan::build(source).map_err(|source| AddSliceAgreementError::Plan { source })?;
    let translation = AddSliceArtifact::new(source.bundle(), source.ast(), plan.clone())
        .cid()
        .map_err(|source| AddSliceAgreementError::Plan { source })?;
    let program = parameter_add_program();
    let init = kernel_cid(kernel, "initial")?;
    let mut staged = kernel.fork();
    let checked =
        prove_add_program_agreement(&mut staged, &program, bool_ty, word_ty, add, left, right)
            .map_err(|source| AddSliceAgreementError::Semantics { source })?;
    let output = kernel_cid(&staged, "output")?;
    *kernel = staged;
    Ok(AddSliceAgreement {
        plan,
        program,
        checked,
        cids: PipelineCids::new(source.ast(), init, translation, output),
    })
}

fn kernel_cid(kernel: &Kernel, stage: &'static str) -> Result<Cid, AddSliceAgreementError> {
    let mut bytes = Vec::new();
    wire::serialize(kernel.arena(), &mut bytes)
        .map_err(|source| AddSliceAgreementError::KernelEncode { stage, source })?;
    Ok(drisl::address(CidCodec::Raw, CidHash::Sha256, &bytes))
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
    prove_add_program_agreement(
        kernel,
        &parameter_add_program(),
        bool_ty,
        word_ty,
        add,
        left,
        right,
    )
}

/// Constructs a direct add route and proves equality with one program route.
///
/// # Errors
///
/// Returns an error under the same conditions as
/// [`prove_parameter_add_agreement`]. The kernel is unchanged on failure.
pub fn prove_add_program_agreement(
    kernel: &mut Kernel,
    program: &Program<ParameterInstruction<AddOperation>>,
    bool_ty: Ref,
    word_ty: Ref,
    add: Ref,
    left: Ref,
    right: Ref,
) -> Result<AddRouteAgreement, AddSemanticsError> {
    if program != &parameter_add_program() {
        return Err(AddSemanticsError::UnsupportedProgram);
    }
    let mut staged = kernel.fork();

    // Route A is authored directly from the selected semantic operation.
    let direct_partial = staged
        .app(add, left)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let direct = staged
        .app(direct_partial, right)
        .map_err(|source| AddSemanticsError::Kernel { source })?;

    // Route B represents the selected program as higher-order data inside HOL,
    // then evaluates it solely through checked application and beta evidence.
    let internal_program = internal_add_program(&mut staged, add, word_ty)?;
    let applied_add = beta_apply(&mut staged, internal_program, add)?;
    let applied_left = beta_apply_after(&mut staged, applied_add, left, "left")?;
    let applied_right = beta_apply_after(&mut staged, applied_left, right, "right")?;
    let interpreted = applied_right.input;
    let same_normal = join_same_syntax(&mut staged, applied_right.output, direct)
        .map_err(|source| AddSemanticsError::Syntax { source })?;
    let interpreted_to_direct = staged
        .syn_trans(None, applied_right.fact, same_normal)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let result_same = staged
        .syn_symm(None, interpreted_to_direct)
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
            SynRel::Conv,
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
        program: internal_program,
        direct,
        interpreted,
        proposition,
        theorem: reflexive.theorem,
    })
}

fn internal_add_program(
    kernel: &mut Kernel,
    add: Ref,
    word_ty: Ref,
) -> Result<Ref, AddSemanticsError> {
    let add_ty = kernel
        .classifier(add)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let add_binder = kernel
        .tm_fv(
            kernel
                .fresh_name(&[add, word_ty])
                .map_err(|source| AddSemanticsError::Kernel { source })?,
            add_ty,
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let left_binder = kernel
        .tm_fv(
            kernel
                .fresh_name(&[add_binder])
                .map_err(|source| AddSemanticsError::Kernel { source })?,
            word_ty,
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let right_binder = kernel
        .tm_fv(
            kernel
                .fresh_name(&[left_binder])
                .map_err(|source| AddSemanticsError::Kernel { source })?,
            word_ty,
        )
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let partial = kernel
        .app(add_binder, left_binder)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let body = kernel
        .app(partial, right_binder)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let with_right = kernel
        .lam(right_binder, body)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let with_left = kernel
        .lam(left_binder, with_right)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let program = kernel
        .lam(add_binder, with_left)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    Ok(program)
}

#[derive(Clone, Copy)]
struct Reduction {
    input: Ref,
    output: Ref,
    fact: SynFactId,
}

fn beta_apply(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<Reduction, AddSemanticsError> {
    let input = kernel
        .app(function, argument)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let children = kernel
        .arena()
        .children(function)
        .ok_or(AddSemanticsError::UnsupportedProgram)?
        .collect::<Vec<_>>();
    let [binder, body] = children.as_slice() else {
        return Err(AddSemanticsError::UnsupportedProgram);
    };
    let substitution = substitute(kernel, *binder, argument, *body)
        .map_err(|source| AddSemanticsError::Substitution { source })?;
    let fact = kernel
        .tm_beta_fact(None, input, substitution.fact)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    kernel
        .union_syn_fact(fact)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    Ok(Reduction {
        input,
        output: substitution.output,
        fact,
    })
}

fn beta_apply_after(
    kernel: &mut Kernel,
    previous: Reduction,
    argument: Ref,
    stage: &'static str,
) -> Result<Reduction, AddSemanticsError> {
    let input = kernel
        .app(previous.input, argument)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let tail = beta_apply(kernel, previous.output, argument)?;
    let argument_same = kernel
        .syn_refl(None, SynRel::Syn, argument)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    let head = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            input,
            tail.input,
            &[previous.fact, argument_same],
        )
        .map_err(|source| AddSemanticsError::BetaCongruence { stage, source })?;
    let fact = kernel
        .syn_trans(None, head, tail.fact)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    kernel
        .union_syn_fact(fact)
        .map_err(|source| AddSemanticsError::Kernel { source })?;
    Ok(Reduction {
        input,
        output: tail.output,
        fact,
    })
}
