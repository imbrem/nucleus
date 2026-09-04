//! Denotational primitives for a pure unary subset of WebAssembly.
//!
//! A semantic instance supplies checked HOL operations mapping structural
//! program terms to pure scalar endofunctions and composing program terms.
//! This module constructs propositions and equality proofs; it never executes
//! Wasm or asserts that a supplied interpretation agrees with `SpecTec`.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, ThmId};
use covalence_logic_hol_derived::{
    EqualityError, SyntaxError, equality_symmetry, equality_transitivity, join_alpha_equivalent,
    join_same_syntax,
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

/// Checked denotational vocabulary for pure scalar endofunctions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PureWasmSemantics {
    program_ty: Ref,
    scalar_kind: WasmScalarKind,
    scalar_ty: Ref,
    function_ty: Ref,
    bool_ty: Ref,
    denotation: Ref,
    compose: Ref,
}

impl PureWasmSemantics {
    /// Validates a pure denotation and structural composition operation.
    ///
    /// `denotation` must have classifier `program -> scalar -> scalar`;
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
        let function_ty = staged.ty_arr(scalar_ty, scalar_ty)?;
        let denotation_ty = staged.ty_arr(program_ty, function_ty)?;
        require_classifier_mut(&mut staged, denotation, denotation_ty)?;
        let compose_tail = staged.ty_arr(program_ty, program_ty)?;
        let compose_ty = staged.ty_arr(program_ty, compose_tail)?;
        require_classifier_mut(&mut staged, compose, compose_ty)?;
        *kernel = staged;
        Ok(Self {
            program_ty,
            scalar_kind,
            scalar_ty,
            function_ty,
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

    /// Returns the checked pure scalar function denoted by `program`.
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
        require_classifier(&staged, denotation, self.function_ty)?;
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

    /// Observes a pure program at one scalar input.
    ///
    /// # Errors
    ///
    /// Returns an error unless the scalar has the configured kind or checked
    /// application fails. `kernel` is unchanged on failure.
    pub fn observe(
        self,
        kernel: &mut Kernel,
        program: PureWasmProgram,
        input: WasmScalar,
    ) -> Result<WasmScalar, KernelError> {
        if input.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm observation scalar kind",
            });
        }
        let mut staged = kernel.fork();
        let denotation = self.denotation(&mut staged, program)?;
        let output = staged.app(denotation, input.term())?;
        require_classifier(&staged, output, self.scalar_ty)?;
        *kernel = staged;
        Ok(WasmScalar::from_checked(self.scalar_kind, output))
    }

    /// Constructs the semantic law for structural function composition.
    ///
    /// The result states that the denotation of `first; second` equals
    /// `fun x => denote(second) (denote(first) x)`. It is an explicit
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
            self.function_ty,
            self.denotation,
            self.compose,
            first.0,
            second.0,
        ])?;
        let binder = staged.tm_fv(name, self.scalar_ty)?;
        let intermediate = staged.app(first_denotation, binder)?;
        let output = staged.app(second_denotation, intermediate)?;
        let semantic_composition = staged.lam_at(self.function_ty, binder, output)?;
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

    /// Specializes observational equivalence to equality at one scalar input.
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
    ) -> Result<Evidence, PureWasmProofError> {
        if input.kind() != self.scalar_kind {
            return Err(KernelError::InvalidTheoremRule {
                rule: "pure Wasm equivalence scalar kind",
            }
            .into());
        }
        let mut staged = kernel.fork();
        let expected = self.equivalent(&mut staged, left, right)?;
        let equivalence = align_positive(&mut staged, equivalence, expected)?;
        let pointwise = staged.ap_thm(equivalence, input.term())?;
        *kernel = staged;
        Ok(Evidence {
            proposition: pointwise.equality,
            theorem: pointwise.theorem,
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
        let expected = staged.ty_arr(pure.program_ty, pure.function_ty)?;
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
        let function_ty = kernel.ty_arr(scalar_types.i32, scalar_types.i32).unwrap();
        let denotation_ty = kernel.ty_arr(program_ty, function_ty).unwrap();
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
        let observed = semantics
            .prove_observation_equal(&mut kernel, reflexive.theorem, left, left, input)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, observed)
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
        assert!(semantics.observe(&mut kernel, left, wrong).is_err());
        assert_eq!(kernel.arena(), &before);
    }
}
