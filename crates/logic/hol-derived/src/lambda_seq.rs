//! Experimental subtyping-free lambda-seq embedded in checked HOL syntax.
//!
//! Rust owns only the untrusted surface AST and elaboration policy. Object
//! types, variables, instruction denotations, monad operations, elaborated
//! programs, and equation statements are all resident HOL [`Ref`] values.
//! This module adds no kernel rule and creates no theorem by itself.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref};

/// One typed primitive instruction with its HOL monadic denotation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Instruction {
    /// Object-language input type.
    pub source: Ref,
    /// Object-language output type.
    pub target: Ref,
    /// HOL term `source → M target`.
    pub denotation: Ref,
}

/// Fully named lambda-seq syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NamedTerm {
    /// A named variable occurrence.
    Var(u64),
    /// A primitive instruction applied to a sequential computation.
    Op(Instruction, Box<Self>),
    /// Sequential binding. `None` denotes an anonymous binder.
    Let(Option<u64>, Box<Self>, Box<Self>),
}

/// Locally nameless lambda-seq syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    /// A free HOL variable.
    Free(Ref),
    /// A de Bruijn index, with zero denoting the nearest binder.
    Bound(usize),
    /// A primitive instruction applied to a sequential computation.
    Op(Instruction, Box<Self>),
    /// Sequential binding.
    Let(Box<Self>, Box<Self>),
}

/// One generating pair in the subtyping-free lambda-seq equational theory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EquationalLaw {
    /// Left program.
    pub left: Term,
    /// Right program.
    pub right: Term,
    /// Exact common object type.
    pub ty: Ref,
}

/// A named variable's HOL syntax and exact object type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Binding {
    /// Resident HOL free-variable term.
    pub variable: Ref,
    /// Exact HOL object type.
    pub ty: Ref,
}

/// Shadowing named context used to lower named terms.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NamedContext(Vec<(u64, Binding)>);

impl NamedContext {
    /// Adds one newest binding.
    pub fn push(&mut self, name: u64, binding: Binding) {
        self.0.push((name, binding));
    }

    /// Removes the newest binding.
    pub fn pop(&mut self) {
        self.0.pop();
    }

    /// Looks up the newest occurrence of a name.
    #[must_use]
    pub fn get(&self, name: u64) -> Option<Binding> {
        self.0
            .iter()
            .rev()
            .find_map(|&(candidate, binding)| (candidate == name).then_some(binding))
    }
}

/// HOL operations interpreting a monad at the object types used by a term.
///
/// Implementations are userspace dictionaries. Every returned reference is
/// checked when it is applied, so a dishonest dictionary can only be rejected
/// or elaborate a different well-typed HOL term.
pub trait MonadModel {
    /// Returns the HOL type `M A`.
    fn computation_type(&self, value_type: Ref) -> Option<Ref>;

    /// Returns the HOL term `A → M A`.
    fn pure(&self, value_type: Ref) -> Option<Ref>;

    /// Returns the curried HOL term `M A → (A → M B) → M B`.
    fn bind(&self, source: Ref, target: Ref) -> Option<Ref>;
}

/// A finite monad dictionary convenient for experiments and serialization.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FiniteMonadModel {
    computations: BTreeMap<Ref, Ref>,
    pure: BTreeMap<Ref, Ref>,
    bind: BTreeMap<(Ref, Ref), Ref>,
}

impl FiniteMonadModel {
    /// Records `M A` and `pure : A → M A`.
    pub fn insert_object(&mut self, value_type: Ref, computation_type: Ref, pure: Ref) {
        self.computations.insert(value_type, computation_type);
        self.pure.insert(value_type, pure);
    }

    /// Records `bind : M A → (A → M B) → M B`.
    pub fn insert_bind(&mut self, source: Ref, target: Ref, bind: Ref) {
        self.bind.insert((source, target), bind);
    }
}

impl MonadModel for FiniteMonadModel {
    fn computation_type(&self, value_type: Ref) -> Option<Ref> {
        self.computations.get(&value_type).copied()
    }

    fn pure(&self, value_type: Ref) -> Option<Ref> {
        self.pure.get(&value_type).copied()
    }

    fn bind(&self, source: Ref, target: Ref) -> Option<Ref> {
        self.bind.get(&(source, target)).copied()
    }
}

/// A well-typed lambda-seq term and its exact object type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TypedTerm {
    /// Exact object type derived by the syntax-directed rules.
    pub ty: Ref,
}

/// A monadic HOL denotation and its exact value/computation types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Denotation {
    /// Object-language result type `A`.
    pub value_type: Ref,
    /// HOL computation type `M A`.
    pub computation_type: Ref,
    /// Resident HOL term of type `M A`.
    pub term: Ref,
}

/// One HOL equality statement generated by the lambda-seq equational API.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Equation {
    /// Left monadic denotation.
    pub left: Denotation,
    /// Right monadic denotation.
    pub right: Denotation,
    /// Resident HOL Boolean term `left = right`.
    pub proposition: Ref,
}

/// Failure to type, lower, or denote an embedded lambda-seq term.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum LambdaSeqError {
    /// A checked HOL operation rejected the proposed syntax.
    #[snafu(display("lambda-seq HOL construction was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Structurally equal HOL classifiers could not be certified.
    #[snafu(display("lambda-seq classifier transport failed: {source}"))]
    Syntax {
        /// Underlying userspace syntax-certificate failure.
        source: crate::SyntaxError,
    },
    /// A named variable is absent from the current context.
    #[snafu(display("lambda-seq variable {name} is unbound"))]
    UnboundName {
        /// Missing variable name.
        name: u64,
    },
    /// A de Bruijn index is outside the current binder stack.
    #[snafu(display("lambda-seq bound index {index} exceeds depth {depth}"))]
    UnboundIndex {
        /// Rejected index.
        index: usize,
        /// Available binder depth.
        depth: usize,
    },
    /// An instruction argument has the wrong exact object type.
    #[snafu(display("lambda-seq instruction argument has the wrong type"))]
    InstructionType,
    /// The monad dictionary has no entry for an object type or type pair.
    #[snafu(display("lambda-seq monad dictionary is incomplete"))]
    MissingMonadOperation,
    /// Two proposed equation endpoints have different result types.
    #[snafu(display("lambda-seq equation endpoints have different types"))]
    EquationType,
    /// A named context annotation disagrees with its HOL variable classifier.
    #[snafu(display("lambda-seq named binding has the wrong type"))]
    ContextType,
    /// Let-beta was requested for an effectful value.
    #[snafu(display("lambda-seq let-beta requires a pure value"))]
    EffectfulBeta,
}

impl From<KernelError> for LambdaSeqError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<crate::SyntaxError> for LambdaSeqError {
    fn from(source: crate::SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

impl NamedTerm {
    /// Lowers named syntax to locally nameless syntax while checking variables.
    ///
    /// Anonymous binders occupy a de Bruijn level but are not added to named
    /// lookup.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound name or if checked HOL variable
    /// inspection rejects a resident HOL reference.
    pub fn lower(&self, kernel: &Kernel, context: &NamedContext) -> Result<Term, LambdaSeqError> {
        self.lower_inner(kernel, context, &mut Vec::new())
    }

    fn lower_inner(
        &self,
        kernel: &Kernel,
        context: &NamedContext,
        bound: &mut Vec<(Option<u64>, Ref)>,
    ) -> Result<Term, LambdaSeqError> {
        match self {
            Self::Var(name) => {
                if let Some(index) = bound
                    .iter()
                    .rev()
                    .position(|(candidate, _)| *candidate == Some(*name))
                {
                    Ok(Term::Bound(index))
                } else {
                    let binding = context
                        .get(*name)
                        .ok_or(LambdaSeqError::UnboundName { name: *name })?;
                    let actual = kernel.classifier(binding.variable)?;
                    if !kernel.equivalent(actual, binding.ty)? {
                        return Err(LambdaSeqError::ContextType);
                    }
                    Ok(Term::Free(binding.variable))
                }
            }
            Self::Op(instruction, argument) => Ok(Term::Op(
                *instruction,
                Box::new(argument.lower_inner(kernel, context, bound)?),
            )),
            Self::Let(name, value, body) => {
                let value = value.lower_inner(kernel, context, bound)?;
                let bound_types = bound.iter().map(|&(_, ty)| ty).collect::<Vec<_>>();
                let value_type = value.type_check(kernel, &bound_types)?;
                bound.push((*name, value_type));
                let lowered_body = body.lower_inner(kernel, context, bound)?;
                bound.pop();
                Ok(Term::Let(Box::new(value), Box::new(lowered_body)))
            }
        }
    }
}

impl Term {
    /// Whether this term uses only instructions accepted by `instruction_is_pure`.
    #[must_use]
    pub fn is_pure(&self, instruction_is_pure: &impl Fn(Instruction) -> bool) -> bool {
        match self {
            Self::Free(_) | Self::Bound(_) => true,
            Self::Op(instruction, argument) => {
                instruction_is_pure(*instruction) && argument.is_pure(instruction_is_pure)
            }
            Self::Let(value, body) => {
                value.is_pure(instruction_is_pure) && body.is_pure(instruction_is_pure)
            }
        }
    }

    /// Applies the exact syntax-directed, subtyping-free typing rules.
    ///
    /// # Errors
    ///
    /// Returns an error for an out-of-scope variable, a mismatched instruction
    /// argument, or an invalid resident HOL reference.
    pub fn type_check(&self, kernel: &Kernel, bound: &[Ref]) -> Result<Ref, LambdaSeqError> {
        match self {
            Self::Free(variable) => Ok(kernel.classifier(*variable)?),
            Self::Bound(index) => {
                bound
                    .iter()
                    .rev()
                    .nth(*index)
                    .copied()
                    .ok_or(LambdaSeqError::UnboundIndex {
                        index: *index,
                        depth: bound.len(),
                    })
            }
            Self::Op(instruction, argument) => {
                let argument_type = argument.type_check(kernel, bound)?;
                if !kernel.equivalent(argument_type, instruction.source)? {
                    return Err(LambdaSeqError::InstructionType);
                }
                Ok(instruction.target)
            }
            Self::Let(value, body) => {
                let value_type = value.type_check(kernel, bound)?;
                let mut body_bound = bound.to_vec();
                body_bound.push(value_type);
                body.type_check(kernel, &body_bound)
            }
        }
    }

    /// Elaborates the syntax-directed typing derivation and monadic semantics
    /// to a resident HOL term.
    ///
    /// Every application and lambda is submitted to the checked kernel. The
    /// method is transactional: rejection leaves `kernel` unchanged.
    ///
    /// # Errors
    ///
    /// Returns an error if the term is ill-scoped or ill-typed, the monad
    /// dictionary is incomplete, or any supplied HOL operation has the wrong
    /// classifier.
    pub fn denote(
        &self,
        kernel: &mut Kernel,
        model: &impl MonadModel,
    ) -> Result<Denotation, LambdaSeqError> {
        let mut staged = kernel.fork();
        let result = self.denote_inner(&mut staged, model, &[])?;
        *kernel = staged;
        Ok(result)
    }

    /// Elaborates with an explicit outer de Bruijn environment.
    ///
    /// The environment is ordered from oldest to newest, as in
    /// [`type_check`](Self::type_check). Elaboration remains transactional.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`denote`](Self::denote), including a
    /// mismatch between a binding annotation and its HOL classifier.
    pub fn denote_in(
        &self,
        kernel: &mut Kernel,
        model: &impl MonadModel,
        bound: &[Binding],
    ) -> Result<Denotation, LambdaSeqError> {
        for binding in bound {
            let actual = kernel.classifier(binding.variable)?;
            if !kernel.equivalent(actual, binding.ty)? {
                return Err(LambdaSeqError::ContextType);
            }
        }
        let mut staged = kernel.fork();
        let result = self.denote_inner(&mut staged, model, bound)?;
        *kernel = staged;
        Ok(result)
    }

    fn denote_inner(
        &self,
        kernel: &mut Kernel,
        model: &impl MonadModel,
        bound: &[Binding],
    ) -> Result<Denotation, LambdaSeqError> {
        match self {
            Self::Free(variable) => {
                let value_type = kernel.classifier(*variable)?;
                pure_value(kernel, model, value_type, *variable)
            }
            Self::Bound(index) => {
                let binding = bound.iter().rev().nth(*index).copied().ok_or(
                    LambdaSeqError::UnboundIndex {
                        index: *index,
                        depth: bound.len(),
                    },
                )?;
                pure_value(kernel, model, binding.ty, binding.variable)
            }
            Self::Op(instruction, argument) => {
                let argument = argument.denote_inner(kernel, model, bound)?;
                if !kernel.equivalent(argument.value_type, instruction.source)? {
                    return Err(LambdaSeqError::InstructionType);
                }
                bind_computation(
                    kernel,
                    model,
                    argument,
                    instruction.target,
                    instruction.denotation,
                )
            }
            Self::Let(value, body) => {
                let value = value.denote_inner(kernel, model, bound)?;
                let binder_name = kernel.fresh_name(&[value.term])?;
                let variable = kernel.tm_fv(binder_name, value.value_type)?;
                let mut body_bound = bound.to_vec();
                body_bound.push(Binding {
                    variable,
                    ty: value.value_type,
                });
                let body = body.denote_inner(kernel, model, &body_bound)?;
                let continuation = kernel.lam(variable, body.term)?;
                bind_computation(kernel, model, value, body.value_type, continuation)
            }
        }
    }
}

impl EquationalLaw {
    /// Constructs pure let-beta: `let x = value; body = body[value/x]`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `value` is pure and both endpoints have the
    /// same exact type under `bound`.
    pub fn let_beta(
        kernel: &Kernel,
        bound: &[Ref],
        value: Term,
        body: Term,
        instruction_is_pure: &impl Fn(Instruction) -> bool,
    ) -> Result<Self, LambdaSeqError> {
        if !value.is_pure(instruction_is_pure) {
            return Err(LambdaSeqError::EffectfulBeta);
        }
        let right = instantiate(&body, &value, 0);
        Self::checked(
            kernel,
            bound,
            Term::Let(Box::new(value), Box::new(body)),
            right,
        )
    }

    /// Constructs let-eta: `let x = term; x = term`.
    ///
    /// # Errors
    ///
    /// Returns an error unless both endpoints have the same exact type.
    pub fn let_eta(kernel: &Kernel, bound: &[Ref], term: Term) -> Result<Self, LambdaSeqError> {
        let left = Term::Let(Box::new(term.clone()), Box::new(Term::Bound(0)));
        Self::checked(kernel, bound, left, term)
    }

    /// Reassociates an instruction through bind.
    ///
    /// `let y = op f argument; body` becomes
    /// `let x = argument; let y = op f x; body`.
    ///
    /// # Errors
    ///
    /// Returns an error unless both endpoints have the same exact type.
    pub fn bind_op(
        kernel: &Kernel,
        bound: &[Ref],
        instruction: Instruction,
        argument: Term,
        body: Term,
    ) -> Result<Self, LambdaSeqError> {
        let right_body = shift(&body, 1, 1);
        let left = Term::Let(
            Box::new(Term::Op(instruction, Box::new(argument.clone()))),
            Box::new(body),
        );
        let right = Term::Let(
            Box::new(argument),
            Box::new(Term::Let(
                Box::new(Term::Op(instruction, Box::new(Term::Bound(0)))),
                Box::new(right_body),
            )),
        );
        Self::checked(kernel, bound, left, right)
    }

    /// Constructs associativity of sequential let.
    ///
    /// # Errors
    ///
    /// Returns an error unless both endpoints have the same exact type.
    pub fn bind_let(
        kernel: &Kernel,
        bound: &[Ref],
        first: Term,
        second: Term,
        third: Term,
    ) -> Result<Self, LambdaSeqError> {
        let right_third = shift(&third, 1, 1);
        let left = Term::Let(
            Box::new(Term::Let(Box::new(first.clone()), Box::new(second.clone()))),
            Box::new(third),
        );
        let right = Term::Let(
            Box::new(first),
            Box::new(Term::Let(Box::new(second), Box::new(right_third))),
        );
        Self::checked(kernel, bound, left, right)
    }

    fn checked(
        kernel: &Kernel,
        bound: &[Ref],
        left: Term,
        right: Term,
    ) -> Result<Self, LambdaSeqError> {
        let ty = left.type_check(kernel, bound)?;
        let right_type = right.type_check(kernel, bound)?;
        if !kernel.equivalent(ty, right_type)? {
            return Err(LambdaSeqError::EquationType);
        }
        Ok(Self { left, right, ty })
    }

    /// Denotes both endpoints and builds their HOL equality statement.
    ///
    /// # Errors
    ///
    /// Returns an error if either denotation is rejected, the monad dictionary
    /// is incomplete, or HOL equality construction fails.
    pub fn denote(
        &self,
        kernel: &mut Kernel,
        bool_type: Ref,
        model: &impl MonadModel,
        bound: &[Binding],
    ) -> Result<Equation, LambdaSeqError> {
        let mut staged = kernel.fork();
        let left = self.left.denote_inner(&mut staged, model, bound)?;
        let right = self.right.denote_inner(&mut staged, model, bound)?;
        let result = equation(&mut staged, bool_type, left, right)?;
        *kernel = staged;
        Ok(result)
    }
}

fn shift(term: &Term, amount: usize, cutoff: usize) -> Term {
    match term {
        Term::Free(variable) => Term::Free(*variable),
        Term::Bound(index) => Term::Bound(if *index >= cutoff {
            index + amount
        } else {
            *index
        }),
        Term::Op(instruction, argument) => {
            Term::Op(*instruction, Box::new(shift(argument, amount, cutoff)))
        }
        Term::Let(value, body) => Term::Let(
            Box::new(shift(value, amount, cutoff)),
            Box::new(shift(body, amount, cutoff + 1)),
        ),
    }
}

fn instantiate(term: &Term, value: &Term, depth: usize) -> Term {
    match term {
        Term::Free(variable) => Term::Free(*variable),
        Term::Bound(index) if *index == depth => shift(value, depth, 0),
        Term::Bound(index) if *index > depth => Term::Bound(index - 1),
        Term::Bound(index) => Term::Bound(*index),
        Term::Op(instruction, argument) => {
            Term::Op(*instruction, Box::new(instantiate(argument, value, depth)))
        }
        Term::Let(bound_value, body) => Term::Let(
            Box::new(instantiate(bound_value, value, depth)),
            Box::new(instantiate(body, value, depth + 1)),
        ),
    }
}

fn pure_value(
    kernel: &mut Kernel,
    model: &impl MonadModel,
    value_type: Ref,
    value: Ref,
) -> Result<Denotation, LambdaSeqError> {
    let computation_type = model
        .computation_type(value_type)
        .ok_or(LambdaSeqError::MissingMonadOperation)?;
    let pure = model
        .pure(value_type)
        .ok_or(LambdaSeqError::MissingMonadOperation)?;
    let term = compatible_app(kernel, pure, value)?;
    let actual = kernel.classifier(term)?;
    if !kernel.equivalent(actual, computation_type)? {
        return Err(LambdaSeqError::MissingMonadOperation);
    }
    Ok(Denotation {
        value_type,
        computation_type,
        term,
    })
}

fn bind_computation(
    kernel: &mut Kernel,
    model: &impl MonadModel,
    input: Denotation,
    target: Ref,
    continuation: Ref,
) -> Result<Denotation, LambdaSeqError> {
    let computation_type = model
        .computation_type(target)
        .ok_or(LambdaSeqError::MissingMonadOperation)?;
    let bind = model
        .bind(input.value_type, target)
        .ok_or(LambdaSeqError::MissingMonadOperation)?;
    let partially_applied = compatible_app(kernel, bind, input.term)?;
    let term = compatible_app(kernel, partially_applied, continuation)?;
    let actual = kernel.classifier(term)?;
    if !kernel.equivalent(actual, computation_type)? {
        return Err(LambdaSeqError::MissingMonadOperation);
    }
    Ok(Denotation {
        value_type: target,
        computation_type,
        term,
    })
}

fn compatible_app(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<Ref, LambdaSeqError> {
    match kernel.app(function, argument) {
        Ok(application) => Ok(application),
        Err(KernelError::ClassifierMismatch { expected, actual }) => {
            crate::join_same_syntax(kernel, expected, actual)?;
            Ok(kernel.app(function, argument)?)
        }
        Err(source) => Err(source.into()),
    }
}

/// Builds the HOL equality statement for two monadic denotations.
///
/// This represents one equation in the lambda-seq theory; it does not assert
/// the equation. A monad model may prove it using its HOL-resident laws.
///
/// # Errors
///
/// Returns an error if the endpoints have different computation types or the
/// checked HOL equality constructor rejects them.
pub fn equation(
    kernel: &mut Kernel,
    bool_type: Ref,
    left: Denotation,
    right: Denotation,
) -> Result<Equation, LambdaSeqError> {
    if !kernel.equivalent(left.value_type, right.value_type)?
        || !kernel.equivalent(left.computation_type, right.computation_type)?
    {
        return Err(LambdaSeqError::EquationType);
    }
    let proposition = kernel.eq_at(bool_type, left.computation_type, left.term, right.term)?;
    Ok(Equation {
        left,
        right,
        proposition,
    })
}
