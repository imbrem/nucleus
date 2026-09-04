//! Denotational primitives for a pure unary subset of WebAssembly.
//!
//! A semantic instance supplies checked HOL operations mapping structural
//! program terms to pure input/output relations and composing program terms.
//! This module constructs propositions and equality proofs; it never executes
//! Wasm or asserts that a supplied interpretation agrees with `SpecTec`.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, ThmId, builtin::Op2};
use covalence_logic_hol_derived::{
    EqualityError, ForallError, SyntaxError, equality_symmetry, equality_transitivity, forall_elim,
    join_alpha_equivalent, join_same_syntax,
};

use crate::{Evidence, WasmScalar, WasmScalarKind, WasmScalarTypes};

/// A structural program term in one pure unary denotational semantics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PureWasmProgram(Ref);

impl PureWasmProgram {
    /// Returns the underlying structural program term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.0
    }
}

/// A checked input/output relation used as a pure program specification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PureWasmRelation(Ref);

impl PureWasmRelation {
    /// Returns the underlying `scalar -> scalar -> bool` term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.0
    }
}

/// Checked denotational vocabulary for pure scalar input/output relations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PureWasmSemantics {
    program_ty: Ref,
    scalar_kind: WasmScalarKind,
    scalar_ty: Ref,
    relation_ty: Ref,
    bool_ty: Ref,
    denotation: Ref,
    compose: Ref,
}

impl PureWasmSemantics {
    /// Validates a pure denotation and structural composition operation.
    ///
    /// `denotation` must have classifier
    /// `program -> scalar -> scalar -> bool`;
    /// `compose` must have classifier `program -> program -> program`.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operations have the required compatible
    /// classifiers. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        kernel: &mut Kernel,
        program_ty: Ref,
        scalar_types: WasmScalarTypes,
        scalar_kind: WasmScalarKind,
        bool_ty: Ref,
        denotation: Ref,
        compose: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let scalar_ty = scalar_types.get(scalar_kind);
        let output_predicate_ty = staged.ty_arr(scalar_ty, bool_ty)?;
        let relation_ty = staged.ty_arr(scalar_ty, output_predicate_ty)?;
        let denotation_ty = staged.ty_arr(program_ty, relation_ty)?;
        require_classifier_mut(&mut staged, denotation, denotation_ty)?;
        let compose_tail = staged.ty_arr(program_ty, program_ty)?;
        let compose_ty = staged.ty_arr(program_ty, compose_tail)?;
        require_classifier_mut(&mut staged, compose, compose_ty)?;
        *kernel = staged;
        Ok(Self {
            program_ty,
            scalar_kind,
            scalar_ty,
            relation_ty,
            bool_ty,
            denotation,
            compose,
        })
    }

    /// Checks and wraps one structural program term.
    ///
    /// # Errors
    ///
    /// Returns an error unless `term` has this semantics' program classifier.
    pub fn program(self, kernel: &Kernel, term: Ref) -> Result<PureWasmProgram, KernelError> {
        require_classifier(kernel, term, self.program_ty)?;
        Ok(PureWasmProgram(term))
    }

    /// Checks and wraps an input/output specification relation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `term` has classifier
    /// `scalar -> scalar -> bool` for this semantics.
    pub fn relation(self, kernel: &Kernel, term: Ref) -> Result<PureWasmRelation, KernelError> {
        require_classifier(kernel, term, self.relation_ty)?;
        Ok(PureWasmRelation(term))
    }

    /// Composes `first` followed by `second` as structural program syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application fails. `kernel` is unchanged on
    /// failure.
    pub fn compose(
        self,
        kernel: &mut Kernel,
        first: PureWasmProgram,
        second: PureWasmProgram,
    ) -> Result<PureWasmProgram, KernelError> {
        let mut staged = kernel.fork();
        let partial = staged.app(self.compose, first.0)?;
        let program = staged.app(partial, second.0)?;
        require_classifier(&staged, program, self.program_ty)?;
        *kernel = staged;
        Ok(PureWasmProgram(program))
    }

    /// Returns the checked pure input/output relation denoted by `program`.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application fails. `kernel` is unchanged on
    /// failure.
    pub fn denotation(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let denotation = staged.app(self.denotation, program.0)?;
        require_classifier(&staged, denotation, self.relation_ty)?;
        *kernel = staged;
        Ok(denotation)
    }

    /// Constructs observational equivalence as equality of pure denotations.
    ///
    /// # Errors
    ///
    /// Returns an error if checked denotation or equality construction fails.
    /// `kernel` is unchanged on failure.
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        left: PureWasmProgram,
        right: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let left = self.denotation(&mut staged, left)?;
        let right = self.denotation(&mut staged, right)?;
        let equivalent = staged.eq(self.bool_ty, left, right)?;
        *kernel = staged;
        Ok(equivalent)
    }

    /// Constructs soundness of a program transformation.
    ///
    /// Here soundness means preservation of observational equivalence:
    /// `forall p q. p ≈ q -> transform p ≈ transform q`. This is a generic
    /// schema; the returned proposition is an obligation, not an asserted
    /// theorem.
    ///
    /// # Errors
    ///
    /// Returns an error unless `transform` has classifier
    /// `program -> program`, or checked application, implication, or
    /// quantification fails. `kernel` is unchanged on failure.
    pub fn preserves_equivalence(
        self,
        kernel: &mut Kernel,
        transform: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let transform_ty = staged.ty_arr(self.program_ty, self.program_ty)?;
        require_classifier_mut(&mut staged, transform, transform_ty)?;
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            transform,
        ])?;
        let left_term = staged.tm_fv(name, self.program_ty)?;
        let right_term = staged.tm_fv(
            name.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.program_ty,
        )?;
        let left = PureWasmProgram(left_term);
        let right = PureWasmProgram(right_term);
        let before = self.equivalent(&mut staged, left, right)?;
        let transformed_left = staged.app(transform, left_term)?;
        let transformed_right = staged.app(transform, right_term)?;
        let transformed_left = PureWasmProgram(transformed_left);
        let transformed_right = PureWasmProgram(transformed_right);
        let after = self.equivalent(&mut staged, transformed_left, transformed_right)?;
        let preservation = staged.op2(Op2::Imp, before, after)?;
        let by_right = staged.forall_tm(self.bool_ty, right_term, preservation)?;
        let proposition = staged.forall_tm(self.bool_ty, left_term, by_right)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs extensional refinement of pure return behavior.
    ///
    /// `implementation` refines `specification` when every scalar pair returned
    /// by the implementation is allowed by the specification. Unlike
    /// equivalence, refinement intentionally permits the implementation to
    /// return on fewer inputs; progress can be stated separately.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, implication, or quantification
    /// fails. `kernel` is unchanged on failure.
    pub fn refines(
        self,
        kernel: &mut Kernel,
        implementation: PureWasmProgram,
        specification: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            implementation.0,
            specification.0,
        ])?;
        let input = staged.tm_fv(name, self.scalar_ty)?;
        let output = staged.tm_fv(
            name.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let implementation_returns = self.returns(
            &mut staged,
            implementation,
            WasmScalar::from_checked(self.scalar_kind, input),
            WasmScalar::from_checked(self.scalar_kind, output),
        )?;
        let specification_returns = self.returns(
            &mut staged,
            specification,
            WasmScalar::from_checked(self.scalar_kind, input),
            WasmScalar::from_checked(self.scalar_kind, output),
        )?;
        let implication = staged.op2(Op2::Imp, implementation_returns, specification_returns)?;
        let by_output = staged.forall_tm(self.bool_ty, output, implication)?;
        let proposition = staged.forall_tm(self.bool_ty, input, by_output)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs the proposition that `program` has exactly `specification`
    /// as its pure input/output relation.
    ///
    /// This is equality of checked HOL relation terms, not a Rust-side
    /// comparison or an assumed interpretation fact.
    ///
    /// # Errors
    ///
    /// Returns an error if checked denotation or equality construction fails.
    /// `kernel` is unchanged on failure.
    pub fn specifies(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        specification: PureWasmRelation,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let denotation = self.denotation(&mut staged, program)?;
        let proposition = staged.eq(self.bool_ty, denotation, specification.0)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs the proposition that a pure program returns one scalar
    /// output for one input.
    ///
    /// # Errors
    ///
    /// Returns an error unless the scalar has the configured kind or checked
    /// application fails. `kernel` is unchanged on failure.
    pub fn returns(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        input: WasmScalar,
        output: WasmScalar,
    ) -> Result<Ref, KernelError> {
        if input.kind() != self.scalar_kind || output.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm return scalar kind",
            });
        }
        let mut staged = kernel.fork();
        let denotation = self.denotation(&mut staged, program)?;
        let at_input = staged.app(denotation, input.term())?;
        let proposition = staged.app(at_input, output.term())?;
        require_classifier(&staged, proposition, self.bool_ty)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs the proposition that `program` has no return value for
    /// `input` in this pure semantics.
    ///
    /// For this deliberately small semantics, non-return combines divergence
    /// and any other behavior excluded from the return relation. A later
    /// effectful semantics may distinguish traps and resource exhaustion.
    ///
    /// # Errors
    ///
    /// Returns an error unless the input has the configured kind or checked
    /// application, negation, and quantification succeed. `kernel` is unchanged
    /// on failure.
    pub fn does_not_return(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        input: WasmScalar,
    ) -> Result<Ref, KernelError> {
        if input.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm non-return scalar kind",
            });
        }
        let mut staged = kernel.fork();
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            program.0,
            input.term(),
        ])?;
        let output = staged.tm_fv(name, self.scalar_ty)?;
        let output = WasmScalar::from_checked(self.scalar_kind, output);
        let returns = self.returns(&mut staged, program, input, output)?;
        let does_not_return = staged.op1(covalence_logic_hol::builtin::Op1::Not, returns)?;
        let proposition = staged.forall_tm(self.bool_ty, output.term(), does_not_return)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs the semantic law for structural function composition.
    ///
    /// The result states that the denotation of `first; second` equals
    /// `fun x z => exists y. denote(first) x y /\ denote(second) y z`. It is an explicit
    /// grounding obligation, not a theorem created by this method.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, abstraction, or equality
    /// construction fails. `kernel` is unchanged on failure.
    pub fn composition_law(
        self,
        kernel: &mut Kernel,
        first: PureWasmProgram,
        second: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let composed = self.compose(&mut staged, first, second)?;
        let composed_denotation = self.denotation(&mut staged, composed)?;
        let first_denotation = self.denotation(&mut staged, first)?;
        let second_denotation = self.denotation(&mut staged, second)?;
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            self.compose,
            first.0,
            second.0,
        ])?;
        let input = staged.tm_fv(name, self.scalar_ty)?;
        let output = staged.tm_fv(
            name.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let intermediate = staged.tm_fv(
            name.checked_add(2).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let first_at_input = staged.app(first_denotation, input)?;
        let first_returns = staged.app(first_at_input, intermediate)?;
        let second_at_intermediate = staged.app(second_denotation, intermediate)?;
        let second_returns = staged.app(second_at_intermediate, output)?;
        let path = staged.op2(
            covalence_logic_hol::builtin::Op2::And,
            first_returns,
            second_returns,
        )?;
        let path = staged.exists_tm(intermediate, path)?;
        let by_output = staged.lam(output, path)?;
        let semantic_composition = staged.lam(input, by_output)?;
        require_classifier_mut(&mut staged, semantic_composition, self.relation_ty)?;
        let law = staged.eq(self.bool_ty, composed_denotation, semantic_composition)?;
        *kernel = staged;
        Ok(law)
    }

    /// Proves observational equivalence is reflexive.
    ///
    /// # Errors
    ///
    /// Returns an error if checked denotation, reflexivity, or formula
    /// alignment fails. `kernel` is unchanged on failure.
    pub fn prove_reflexive(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let denotation = self.denotation(&mut staged, program)?;
        let reflexive = staged.refl(self.bool_ty, denotation)?;
        let proposition = self.equivalent(&mut staged, program, program)?;
        join_alpha_equivalent(&mut staged, reflexive.equality, proposition)?;
        staged.convert_conclusions(reflexive.theorem, reflexive.equality, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: reflexive.theorem,
            holds: true,
        })
    }

    /// Proves pure return-behavior refinement is reflexive.
    ///
    /// # Errors
    ///
    /// Returns an error if checked implication, universal introduction, or
    /// formula alignment fails. `kernel` is unchanged on failure.
    pub fn prove_refinement_reflexive(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            program.0,
        ])?;
        let input = staged.tm_fv(name, self.scalar_ty)?;
        let output = staged.tm_fv(
            name.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let returns = self.returns(
            &mut staged,
            program,
            WasmScalar::from_checked(self.scalar_kind, input),
            WasmScalar::from_checked(self.scalar_kind, output),
        )?;
        let implication = staged.op2(Op2::Imp, returns, returns)?;
        let assumed = staged.identity(Lit::positive(returns.get()))?;
        let implication_fact = staged.imp_right(assumed, Lit::positive(implication.get()))?;
        let by_output = staged.forall_tm(self.bool_ty, output, implication)?;
        let by_output_fact = staged.forall_intro_at(implication_fact, output, by_output)?;
        let universal = staged.forall_tm(self.bool_ty, input, by_output)?;
        let theorem = staged.forall_intro_at(by_output_fact, input, universal)?;
        let proposition = self.refines(&mut staged, program, program)?;
        join_alpha_equivalent(&mut staged, universal, proposition)?;
        staged.convert_conclusions(theorem, universal, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem,
            holds: true,
        })
    }

    /// Derives directional return refinement from denotational equivalence.
    ///
    /// Every premise of `equivalence` remains visible. Applying this method in
    /// both directions (using [`Self::prove_symmetric`]) yields mutual
    /// refinement without redefining equivalence as a pair of implications.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` proves the exact denotational
    /// equality or checked application, implication, quantification, or formula
    /// alignment fails. `kernel` is unchanged on failure.
    pub fn prove_equivalence_refines(
        self,
        kernel: &mut Kernel,
        equivalence: ThmId,
        implementation: PureWasmProgram,
        specification: PureWasmProgram,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let expected = self.equivalent(&mut staged, implementation, specification)?;
        let equivalence = align_positive(&mut staged, equivalence, expected)?;
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            implementation.0,
            specification.0,
            expected,
        ])?;
        let input = staged.tm_fv(name, self.scalar_ty)?;
        let output = staged.tm_fv(
            name.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let at_input = staged.ap_thm(equivalence, input)?;
        let at_output = staged.ap_thm(at_input.theorem, output)?;
        let assumed = staged.identity(Lit::positive(at_output.left.get()))?;
        let specification_returns = staged.eq_mp(at_output.theorem, assumed)?;
        let implication = staged.op2(Op2::Imp, at_output.left, at_output.right)?;
        let implication_fact =
            staged.imp_right(specification_returns, Lit::positive(implication.get()))?;
        let by_output = staged.forall_tm(self.bool_ty, output, implication)?;
        let by_output_fact = staged.forall_intro_at(implication_fact, output, by_output)?;
        let universal = staged.forall_tm(self.bool_ty, input, by_output)?;
        let theorem = staged.forall_intro_at(by_output_fact, input, universal)?;
        let proposition = self.refines(&mut staged, implementation, specification)?;
        join_alpha_equivalent(&mut staged, universal, proposition)?;
        staged.convert_conclusions(theorem, universal, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem,
            holds: true,
        })
    }

    /// Reverses checked positive observational equivalence.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` proves the expected equality or a
    /// checked equality step fails. `kernel` is unchanged on failure.
    pub fn prove_symmetric(
        self,
        kernel: &mut Kernel,
        equivalence: ThmId,
        left: PureWasmProgram,
        right: PureWasmProgram,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let expected = self.equivalent(&mut staged, left, right)?;
        let aligned = align_positive(&mut staged, equivalence, expected)?;
        let reversed = equality_symmetry(&mut staged, self.bool_ty, aligned)?;
        let proposition = self.equivalent(&mut staged, right, left)?;
        join_alpha_equivalent(&mut staged, reversed.equality, proposition)?;
        staged.convert_conclusions(reversed.theorem, reversed.equality, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: reversed.theorem,
            holds: true,
        })
    }

    /// Composes checked positive observational equivalence theorems.
    ///
    /// # Errors
    ///
    /// Returns an error unless the input theorems prove the expected adjacent
    /// equalities or a checked equality step fails. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_transitive(
        self,
        kernel: &mut Kernel,
        left_middle: ThmId,
        middle_right: ThmId,
        left: PureWasmProgram,
        middle: PureWasmProgram,
        right: PureWasmProgram,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let left_expected = self.equivalent(&mut staged, left, middle)?;
        let left_middle = align_positive(&mut staged, left_middle, left_expected)?;
        let right_expected = self.equivalent(&mut staged, middle, right)?;
        let middle_right = align_positive(&mut staged, middle_right, right_expected)?;
        let composed = equality_transitivity(&mut staged, self.bool_ty, left_middle, middle_right)?;
        let proposition = self.equivalent(&mut staged, left, right)?;
        join_alpha_equivalent(&mut staged, composed.equality, proposition)?;
        staged.convert_conclusions(composed.theorem, composed.equality, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: composed.theorem,
            holds: true,
        })
    }

    /// Specializes observational equivalence to equality of return
    /// propositions at one input/output pair.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` proves the expected equality, the
    /// input has the configured kind, or checked application fails. `kernel`
    /// is unchanged on failure.
    pub fn prove_observation_equal(
        self,
        kernel: &mut Kernel,
        equivalence: ThmId,
        left: PureWasmProgram,
        right: PureWasmProgram,
        input: WasmScalar,
        output: WasmScalar,
    ) -> Result<Evidence, PureWasmProofError> {
        if input.kind() != self.scalar_kind || output.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm equivalence scalar kind",
            }
            .into());
        }
        let mut staged = kernel.fork();
        let expected = self.equivalent(&mut staged, left, right)?;
        let equivalence = align_positive(&mut staged, equivalence, expected)?;
        let at_input = staged.ap_thm(equivalence, input.term())?;
        let pointwise = staged.ap_thm(at_input.theorem, output.term())?;
        *kernel = staged;
        Ok(Evidence {
            proposition: pointwise.equality,
            theorem: pointwise.theorem,
            holds: true,
        })
    }

    /// Transports a checked specification-return fact into a program-return
    /// fact.
    ///
    /// `specification_fact` proves that the program's denotation equals the
    /// supplied relation. `returns_fact` proves that relation at the concrete
    /// input/output pair. Every premise of both facts remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorems have their exact positive
    /// conclusions, the scalar kinds match, or checked equality transport
    /// fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_returns_from_specification(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        specification: PureWasmRelation,
        input: WasmScalar,
        output: WasmScalar,
        specification_fact: ThmId,
        returns_fact: ThmId,
    ) -> Result<Evidence, PureWasmProofError> {
        if input.kind() != self.scalar_kind || output.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm specification scalar kind",
            }
            .into());
        }
        let mut staged = kernel.fork();
        let specification_claim = self.specifies(&mut staged, program, specification)?;
        let specification_fact =
            align_positive(&mut staged, specification_fact, specification_claim)?;
        let at_input = staged.ap_thm(specification_fact, input.term())?;
        let at_output = staged.ap_thm(at_input.theorem, output.term())?;
        let reversed = equality_symmetry(&mut staged, self.bool_ty, at_output.theorem)?;
        let returns_fact = align_positive(&mut staged, returns_fact, reversed.left)?;
        let theorem = staged.eq_mp(reversed.theorem, returns_fact)?;
        let proposition = self.returns(&mut staged, program, input, output)?;
        join_alpha_equivalent(&mut staged, at_output.left, proposition)?;
        staged.convert_conclusions(theorem, at_output.left, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem,
            holds: true,
        })
    }

    /// Transports checked non-return from a specification relation to a program.
    ///
    /// Both the exact-denotation theorem and the theorem that the relation has
    /// no output for `input` remain visible as premises. This is the branch
    /// needed by partial specifications such as “factorial returns its result
    /// when representable and otherwise does not return.”
    ///
    /// # Errors
    ///
    /// Returns an error unless the supplied theorems prove the exact
    /// specification and non-return propositions, the scalar kind matches, or
    /// a checked equality, quantifier, or propositional step fails. `kernel`
    /// is unchanged on failure.
    pub fn prove_non_return_from_specification(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        specification: PureWasmRelation,
        input: WasmScalar,
        specification_fact: ThmId,
        non_return_fact: ThmId,
    ) -> Result<Evidence, PureWasmProofError> {
        if input.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm specification scalar kind",
            }
            .into());
        }
        let mut staged = kernel.fork();
        let specification_claim = self.specifies(&mut staged, program, specification)?;
        let specification_fact =
            align_positive(&mut staged, specification_fact, specification_claim)?;
        let name = staged.fresh_name(&[
            self.program_ty,
            self.scalar_ty,
            self.relation_ty,
            self.denotation,
            program.0,
            specification.0,
            input.term(),
        ])?;
        let output = staged.tm_fv(name, self.scalar_ty)?;
        let scalar_output = WasmScalar::from_checked(self.scalar_kind, output);

        let relation_at_input = staged.app(specification.0, input.term())?;
        let relation_returns = staged.app(relation_at_input, output)?;
        let relation_non_return = {
            let denied = staged.op1(covalence_logic_hol::builtin::Op1::Not, relation_returns)?;
            staged.forall_tm(self.bool_ty, output, denied)?
        };
        let non_return_fact = align_positive(&mut staged, non_return_fact, relation_non_return)?;
        let denied = forall_elim(&mut staged, non_return_fact, output)?;
        let denied =
            staged.flatten_conclusion(denied.theorem, Lit::positive(denied.proposition.get()))?;

        let at_input = staged.ap_thm(specification_fact, input.term())?;
        let at_output = staged.ap_thm(at_input.theorem, output)?;
        let implementation_returns = self.returns(&mut staged, program, input, scalar_output)?;
        join_alpha_equivalent(&mut staged, at_output.left, implementation_returns)?;
        let assumed = staged.identity(Lit::positive(at_output.left.get()))?;
        let specification_returns = staged.eq_mp(at_output.theorem, assumed)?;
        join_alpha_equivalent(&mut staged, at_output.right, relation_returns)?;
        staged.convert_conclusions(specification_returns, at_output.right, relation_returns)?;
        let contradiction = staged.resolve(
            specification_returns,
            denied,
            Lit::positive(relation_returns.get()),
        )?;
        staged.not_right(contradiction, Lit::positive(at_output.left.get()))?;
        let implementation_denied = staged.op1(
            covalence_logic_hol::builtin::Op1::Not,
            at_output.left,
        )?;
        let theorem =
            staged.fold_conclusion(contradiction, Lit::positive(implementation_denied.get()))?;
        let universal = staged.forall_tm(self.bool_ty, output, implementation_denied)?;
        let theorem = staged.forall_intro_at(theorem, output, universal)?;
        let proposition = self.does_not_return(&mut staged, program, input)?;
        join_alpha_equivalent(&mut staged, universal, proposition)?;
        staged.convert_conclusions(theorem, universal, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem,
            holds: true,
        })
    }
}

/// Single-threaded and multi-threaded denotations of the same pure programs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ThreadedPureWasmSemantics {
    pure: PureWasmSemantics,
    single: Ref,
    multi: Ref,
}

impl ThreadedPureWasmSemantics {
    /// Validates profile-specific denotation functions.
    ///
    /// # Errors
    ///
    /// Returns an error unless both functions have the same
    /// `program -> scalar -> scalar` classifier as the pure denotation.
    /// `kernel` is unchanged on failure.
    pub fn new(
        kernel: &mut Kernel,
        pure: PureWasmSemantics,
        single: Ref,
        multi: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let expected = staged.ty_arr(pure.program_ty, pure.relation_ty)?;
        require_classifier_mut(&mut staged, single, expected)?;
        require_classifier_mut(&mut staged, multi, expected)?;
        *kernel = staged;
        Ok(Self {
            pure,
            single,
            multi,
        })
    }

    /// Constructs equality of single-threaded and multi-threaded denotations.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application or equality construction fails.
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let single = kernel.app(self.single, program.0)?;
        let multi = kernel.app(self.multi, program.0)?;
        kernel.eq(self.pure.bool_ty, single, multi)
    }

    /// Constructs agreement of the single-threaded profile with the pure
    /// denotation.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application or equality construction fails.
    pub fn single_agrees(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let single = kernel.app(self.single, program.0)?;
        let pure = self.pure.denotation(kernel, program)?;
        kernel.eq(self.pure.bool_ty, single, pure)
    }

    /// Constructs agreement of the multi-threaded profile with the pure
    /// denotation.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application or equality construction fails.
    pub fn multi_agrees(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
    ) -> Result<Ref, KernelError> {
        let multi = kernel.app(self.multi, program.0)?;
        let pure = self.pure.denotation(kernel, program)?;
        kernel.eq(self.pure.bool_ty, multi, pure)
    }

    /// Proves single-/multi-threaded equivalence through their shared pure
    /// denotation.
    ///
    /// Both agreement theorem premises remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorems prove their exact agreement
    /// propositions or a checked equality step fails. `kernel` is unchanged on
    /// failure.
    pub fn prove_equivalent(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        single_agrees: ThmId,
        multi_agrees: ThmId,
    ) -> Result<Evidence, PureWasmProofError> {
        let mut staged = kernel.fork();
        let single_claim = self.single_agrees(&mut staged, program)?;
        let single = align_positive(&mut staged, single_agrees, single_claim)?;
        let multi_claim = self.multi_agrees(&mut staged, program)?;
        let multi = align_positive(&mut staged, multi_agrees, multi_claim)?;
        let reverse_multi = equality_symmetry(&mut staged, self.pure.bool_ty, multi)?;
        let composed = equality_transitivity(
            &mut staged,
            self.pure.bool_ty,
            single,
            reverse_multi.theorem,
        )?;
        let proposition = self.equivalent(&mut staged, program)?;
        join_alpha_equivalent(&mut staged, composed.equality, proposition)?;
        staged.convert_conclusions(composed.theorem, composed.equality, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: composed.theorem,
            holds: true,
        })
    }
}

/// Failure to derive a pure-Wasm denotational theorem.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum PureWasmProofError {
    /// A checked HOL operation failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A userspace equality derivation failed.
    #[snafu(transparent)]
    Equality {
        /// Underlying equality failure.
        source: EqualityError,
    },
    /// Checked formulas could not be alpha-aligned.
    #[snafu(transparent)]
    Syntax {
        /// Underlying syntax-certification failure.
        source: SyntaxError,
    },
    /// Universal specialization failed.
    #[snafu(transparent)]
    Forall {
        /// Underlying specialization failure.
        source: ForallError,
    },
}

fn align_positive(kernel: &mut Kernel, theorem: ThmId, target: Ref) -> Result<ThmId, KernelError> {
    let source = {
        let stored = kernel
            .thm()
            .get(theorem)
            .ok_or(KernelError::MissingTheorem { id: theorem })?;
        let mut rows = stored.rhs.rows();
        let Some([literal]) = rows.next() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm positive equality conclusion",
            });
        };
        if rows.next().is_some() || !literal.is_positive() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm positive equality conclusion",
            });
        }
        Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
            rule: "pure Wasm equality conclusion reference",
        })?
    };
    join_alpha_equivalent(kernel, source, target).map_err(|_| KernelError::InvalidTheoremRule {
        rule: "pure Wasm equality conclusion alignment",
    })?;
    let aligned = kernel.copy_theorem(theorem)?;
    kernel.convert_conclusions(aligned, source, target)?;
    Ok(aligned)
}

fn require_classifier(kernel: &Kernel, term: Ref, expected: Ref) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    if kernel.equivalent(actual, expected)? {
        Ok(())
    } else {
        Err(KernelError::ClassifierMismatch { expected, actual })
    }
}

fn require_classifier_mut(
    kernel: &mut Kernel,
    term: Ref,
    expected: Ref,
) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    if kernel.equivalent(actual, expected)? || join_same_syntax(kernel, actual, expected).is_ok() {
        Ok(())
    } else {
        Err(KernelError::ClassifierMismatch { expected, actual })
    }
}

#[cfg(test)]
mod tests {
    use covalence_logic_hol::Lit;

    use super::*;
    use crate::{EvidenceScope, WasmScalars};

    #[test]
    #[allow(clippy::too_many_lines)]
    fn pure_denotations_compose_observe_and_compare_thread_profiles() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let program_ty = kernel.ty_fv(1, star).unwrap();
        let scalar_types = WasmScalarTypes {
            i32: kernel.ty_fv(2, star).unwrap(),
            i64: kernel.ty_fv(3, star).unwrap(),
            f32: kernel.ty_fv(4, star).unwrap(),
            f64: kernel.ty_fv(5, star).unwrap(),
            v128: kernel.ty_fv(6, star).unwrap(),
        };
        let output_predicate_ty = kernel.ty_arr(scalar_types.i32, bool_ty).unwrap();
        let relation_ty = kernel
            .ty_arr(scalar_types.i32, output_predicate_ty)
            .unwrap();
        let denotation_ty = kernel.ty_arr(program_ty, relation_ty).unwrap();
        let denotation = kernel.tm_fv(10, denotation_ty).unwrap();
        let compose_tail = kernel.ty_arr(program_ty, program_ty).unwrap();
        let compose_ty = kernel.ty_arr(program_ty, compose_tail).unwrap();
        let compose = kernel.tm_fv(11, compose_ty).unwrap();
        let semantics = PureWasmSemantics::new(
            &mut kernel,
            program_ty,
            scalar_types,
            WasmScalarKind::I32,
            bool_ty,
            denotation,
            compose,
        )
        .unwrap();
        let left_term = kernel.tm_fv(12, program_ty).unwrap();
        let left = semantics.program(&kernel, left_term).unwrap();
        let middle_term = kernel.tm_fv(13, program_ty).unwrap();
        let middle = semantics.program(&kernel, middle_term).unwrap();
        let composed = semantics.compose(&mut kernel, left, middle).unwrap();
        let transform = kernel.tm_fv(20, compose_tail).unwrap();
        let soundness = semantics
            .preserves_equivalence(&mut kernel, transform)
            .unwrap();
        assert!(
            kernel
                .equivalent(kernel.classifier(soundness).unwrap(), bool_ty)
                .unwrap()
        );
        let law = semantics
            .composition_law(&mut kernel, left, middle)
            .unwrap();
        assert!(
            kernel
                .equivalent(kernel.classifier(law).unwrap(), bool_ty)
                .unwrap()
        );
        assert!(
            kernel
                .equivalent(kernel.classifier(composed.term()).unwrap(), program_ty)
                .unwrap()
        );

        let reflexive = semantics.prove_reflexive(&mut kernel, left).unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, reflexive)
            .unwrap();
        let refinement = semantics
            .prove_refinement_reflexive(&mut kernel, left)
            .unwrap();
        let refinement_from_equivalence = semantics
            .prove_equivalence_refines(&mut kernel, reflexive.theorem, left, left)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, refinement_from_equivalence)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, refinement)
            .unwrap();
        let symmetric = semantics
            .prove_symmetric(&mut kernel, reflexive.theorem, left, left)
            .unwrap();
        let transitive = semantics
            .prove_transitive(
                &mut kernel,
                reflexive.theorem,
                symmetric.theorem,
                left,
                left,
                left,
            )
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, transitive)
            .unwrap();
        let scalars = WasmScalars {
            types: scalar_types,
            bool_ty,
        };
        let input_term = kernel.tm_fv(14, scalar_types.i32).unwrap();
        let input = scalars
            .scalar(&kernel, WasmScalarKind::I32, input_term)
            .unwrap();
        let output_term = kernel.tm_fv(18, scalar_types.i32).unwrap();
        let output = scalars
            .scalar(&kernel, WasmScalarKind::I32, output_term)
            .unwrap();
        let does_not_return = semantics.does_not_return(&mut kernel, left, input).unwrap();
        assert!(
            kernel
                .equivalent(kernel.classifier(does_not_return).unwrap(), bool_ty)
                .unwrap()
        );
        let observed = semantics
            .prove_observation_equal(&mut kernel, reflexive.theorem, left, left, input, output)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, observed)
            .unwrap();

        let specification_term = kernel.tm_fv(19, relation_ty).unwrap();
        let specification = semantics.relation(&kernel, specification_term).unwrap();
        let specification_claim = semantics
            .specifies(&mut kernel, left, specification)
            .unwrap();
        let relation_at_input = kernel.app(specification.term(), input.term()).unwrap();
        let relation_returns = kernel.app(relation_at_input, output.term()).unwrap();
        let specification_fact = kernel
            .identity(Lit::positive(specification_claim.get()))
            .unwrap();
        let returns_fact = kernel
            .identity(Lit::positive(relation_returns.get()))
            .unwrap();
        let program_returns = semantics
            .prove_returns_from_specification(
                &mut kernel,
                left,
                specification,
                input,
                output,
                specification_fact,
                returns_fact,
            )
            .unwrap();
        EvidenceScope::positive(&[specification_claim, relation_returns])
            .check(&kernel, program_returns)
            .unwrap();

        let arbitrary_output = kernel.tm_fv(21, scalar_types.i32).unwrap();
        let relation_at_input = kernel.app(specification.term(), input.term()).unwrap();
        let relation_returns = kernel.app(relation_at_input, arbitrary_output).unwrap();
        let relation_denied = kernel
            .op1(covalence_logic_hol::builtin::Op1::Not, relation_returns)
            .unwrap();
        let relation_non_return = kernel
            .forall_tm(bool_ty, arbitrary_output, relation_denied)
            .unwrap();
        let relation_non_return_fact = kernel
            .identity(Lit::positive(relation_non_return.get()))
            .unwrap();
        let program_non_return = semantics
            .prove_non_return_from_specification(
                &mut kernel,
                left,
                specification,
                input,
                specification_fact,
                relation_non_return_fact,
            )
            .unwrap();
        EvidenceScope::positive(&[specification_claim, relation_non_return])
            .check(&kernel, program_non_return)
            .unwrap();

        let single = kernel.tm_fv(15, denotation_ty).unwrap();
        let multi = kernel.tm_fv(16, denotation_ty).unwrap();
        let threaded =
            ThreadedPureWasmSemantics::new(&mut kernel, semantics, single, multi).unwrap();
        let single_claim = threaded.single_agrees(&mut kernel, left).unwrap();
        let multi_claim = threaded.multi_agrees(&mut kernel, left).unwrap();
        let single_fact = kernel.identity(Lit::positive(single_claim.get())).unwrap();
        let multi_fact = kernel.identity(Lit::positive(multi_claim.get())).unwrap();
        let equivalent = threaded
            .prove_equivalent(&mut kernel, left, single_fact, multi_fact)
            .unwrap();
        EvidenceScope::positive(&[single_claim, multi_claim])
            .check(&kernel, equivalent)
            .unwrap();

        let wrong_term = kernel.tm_fv(17, scalar_types.i64).unwrap();
        let wrong = scalars
            .scalar(&kernel, WasmScalarKind::I64, wrong_term)
            .unwrap();
        let before = kernel.arena().clone();
        assert!(semantics.returns(&mut kernel, left, wrong, output).is_err());
        assert_eq!(kernel.arena(), &before);
    }
}
