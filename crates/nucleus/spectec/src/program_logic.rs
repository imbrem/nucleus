//! Immutable proposition schemas for experiments over program behavior.
//!
//! This module deliberately does not execute WebAssembly. [`CallsAssert`] is
//! an open proposition whose intended meaning is existential: some permitted
//! invocation and imported-I/O behavior reaches the named assertion import.
//! Giving that atom meaning requires a separate interpretation relating
//! program bytes to the `SpecTec` semantics. Closed formulas can already be
//! lowered and proved through checked kernel rules without adding an axiom.

use std::{convert::Infallible, sync::Arc};

use covalence_data_basic::Symbol;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, ThmId,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    ExistsError, ForallError, SyntaxError, forall_elim, introduce_exists, join_alpha_equivalent,
    open_exists,
};

/// A small, immutable, generic proposition schema.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proposition<Atom> {
    /// An open proposition supplied by a semantic interpretation.
    Atom(Atom),
    /// Falsehood.
    False,
    /// Truth.
    True,
    /// Conjunction of two propositions.
    And(Arc<Self>, Arc<Self>),
    /// Disjunction of two propositions.
    Or(Arc<Self>, Arc<Self>),
}

impl<Atom> Proposition<Atom> {
    /// Constructs an atomic proposition.
    pub const fn atom(atom: Atom) -> Self {
        Self::Atom(atom)
    }

    /// Constructs a conjunction without mutating either operand.
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self::And(Arc::new(self), Arc::new(other))
    }

    /// Constructs a disjunction without mutating either operand.
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        Self::Or(Arc::new(self), Arc::new(other))
    }

    /// Maps atoms while preserving proposition shape.
    pub fn map<Mapped>(&self, map: &mut impl FnMut(&Atom) -> Mapped) -> Proposition<Mapped> {
        match self {
            Self::Atom(atom) => Proposition::Atom(map(atom)),
            Self::False => Proposition::False,
            Self::True => Proposition::True,
            Self::And(left, right) => left.map(map).and(right.map(map)),
            Self::Or(left, right) => left.map(map).or(right.map(map)),
        }
    }

    /// Derives a formula from checked, possibly conditional evidence for each
    /// open atom.
    ///
    /// The callback is the explicit semantic interpretation boundary. Its
    /// result must have exactly the claimed positive or negative conclusion;
    /// all theorem premises remain visible and are propagated by checked rules.
    /// Input theorems remain reusable.
    ///
    /// # Errors
    ///
    /// Returns an error if atom evidence has the wrong conclusion or a checked HOL
    /// construction fails.
    pub fn derive_with(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        atom: &mut impl FnMut(&Atom, &mut Kernel, Ref) -> Result<Evidence, KernelError>,
    ) -> Result<Evidence, KernelError> {
        match self {
            Self::Atom(value) => {
                let evidence = atom(value, kernel, bool_ty)?;
                require_conclusion(kernel, evidence)?;
                Ok(evidence)
            }
            Self::False => constant(kernel, bool_ty, false),
            Self::True => constant(kernel, bool_ty, true),
            Self::And(left, right) => {
                let left = left.derive_with(kernel, bool_ty, atom)?;
                let right = right.derive_with(kernel, bool_ty, atom)?;
                establish_and(kernel, left, right)
            }
            Self::Or(left, right) => {
                let left = left.derive_with(kernel, bool_ty, atom)?;
                let right = right.derive_with(kernel, bool_ty, atom)?;
                establish_or(kernel, left, right)
            }
        }
    }

    /// Establishes a formula from premise-free checked atom facts.
    ///
    /// # Errors
    ///
    /// Returns an error if atom evidence is not premise-free and exact, or a
    /// checked HOL construction fails.
    pub fn establish_with(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        atom: &mut impl FnMut(&Atom, &mut Kernel, Ref) -> Result<Established, KernelError>,
    ) -> Result<Established, KernelError> {
        let evidence = self.derive_with(kernel, bool_ty, &mut |value, kernel, bool_ty| {
            let established = atom(value, kernel, bool_ty)?;
            require_exact(kernel, established)?;
            Ok(established.into())
        })?;
        require_premise_free(kernel, evidence)
    }
}

/// An open atom saying a program can call a distinguished assertion import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallsAssert<Program> {
    /// Stable program identity chosen by the surrounding schema.
    pub program: Program,
    /// Imported function treated as the assertion observation.
    pub import: Symbol,
}

/// Generic HOL predicates defining existential assertion reachability.
///
/// `starts program state` includes the existential choices of exported
/// function, arguments, and behavior of imports other than `assert`. `steps`
/// is the reflexive-transitive execution relation. `calls state function`
/// observes a configuration immediately before a host call. A `SpecTec`
/// adapter supplies these predicates; this schema only composes them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AssertionReachability {
    /// Classifier shared by module terms.
    pub program_ty: Ref,
    /// Classifier shared by execution configurations.
    pub state_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Curried predicate `program -> state -> bool`.
    pub starts: Ref,
    /// Curried predicate `state -> state -> bool`.
    pub steps: Ref,
    /// Curried predicate `state -> function -> bool`.
    pub calls: Ref,
}

impl AssertionReachability {
    /// Constructs `callsAssert(program, assert_function)` as an existential
    /// reachability proposition.
    ///
    /// The result is
    /// `exists initial final. starts program initial /\ steps initial final /\
    /// calls final assert_function`. This creates checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible predicate arguments, non-Boolean
    /// results, fresh-name exhaustion, or a rejected checked constructor.
    pub fn calls_assert(
        self,
        kernel: &mut Kernel,
        program: Ref,
        assert_function: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let roots = [
            self.program_ty,
            self.state_ty,
            self.bool_ty,
            self.starts,
            self.steps,
            self.calls,
            program,
            assert_function,
        ];
        let initial_name = staged.fresh_name(&roots)?;
        let final_name = initial_name
            .checked_add(1)
            .ok_or(KernelError::<Infallible>::TooManyNames)?;
        let initial = staged.tm_fv(initial_name, self.state_ty)?;
        let final_state = staged.tm_fv(final_name, self.state_ty)?;

        let starts = apply2(&mut staged, self.starts, program, initial)?;
        let steps = apply2(&mut staged, self.steps, initial, final_state)?;
        let calls = apply2(&mut staged, self.calls, final_state, assert_function)?;
        require_bool(&mut staged, self.bool_ty, starts)?;
        require_bool(&mut staged, self.bool_ty, steps)?;
        require_bool(&mut staged, self.bool_ty, calls)?;
        let reached = staged.op2(Op2::And, steps, calls)?;
        let body = staged.op2(Op2::And, starts, reached)?;
        let body = staged.exists_tm(final_state, body)?;
        let proposition = staged.exists_tm(initial, body)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Abstracts `callsAssert` into a checked `program -> bool` predicate for
    /// one distinguished host function.
    ///
    /// # Errors
    ///
    /// Returns an error if existential reachability or checked abstraction
    /// construction fails. `kernel` is unchanged on failure.
    pub fn predicate(self, kernel: &mut Kernel, assert_function: Ref) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let name = staged.fresh_name(&[
            self.program_ty,
            self.state_ty,
            self.bool_ty,
            self.starts,
            self.steps,
            self.calls,
            assert_function,
        ])?;
        let program = staged.tm_fv(name, self.program_ty)?;
        let body = self.calls_assert(&mut staged, program, assert_function)?;
        let predicate_ty = staged.ty_arr(self.program_ty, self.bool_ty)?;
        let predicate = staged.lam_at(predicate_ty, program, body)?;
        *kernel = staged;
        Ok(predicate)
    }

    /// Constructs the universal negative claim that no admissible execution
    /// reaches the distinguished assertion call.
    ///
    /// This is the HOL negation of [`calls_assert`](Self::calls_assert), not a
    /// conclusion drawn from bounded testing or failure to observe a call.
    /// It creates checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as `calls_assert`, or if the
    /// checked negation constructor rejects the resulting proposition.
    /// `kernel` is unchanged on failure.
    pub fn never_calls_assert(
        self,
        kernel: &mut Kernel,
        program: Ref,
        assert_function: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let positive = self.calls_assert(&mut staged, program, assert_function)?;
        let negative = staged.op1(Op1::Not, positive)?;
        *kernel = staged;
        Ok(negative)
    }

    /// Constructs the claim that a program has no admissible initial state.
    ///
    /// The result is `forall initial. not (starts program initial)`.
    ///
    /// # Errors
    ///
    /// Returns an error for an incompatible program, fresh-name exhaustion, or
    /// a rejected checked constructor. `kernel` is unchanged on failure.
    pub fn no_admissible_start(
        self,
        kernel: &mut Kernel,
        program: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        require_classifier(&mut staged, program, self.program_ty)?;
        let name = staged.fresh_name(&[
            self.program_ty,
            self.state_ty,
            self.bool_ty,
            self.starts,
            program,
        ])?;
        let initial = staged.tm_fv(name, self.state_ty)?;
        let starts = apply2(&mut staged, self.starts, program, initial)?;
        let does_not_start = staged.op1(Op1::Not, starts)?;
        let proposition = staged.forall_tm(self.bool_ty, initial, does_not_start)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Proves negative assertion reachability from absence of admissible starts.
    ///
    /// `no_start_fact` must prove the exact proposition returned by
    /// [`Self::no_admissible_start`]. The proof assumes `callsAssert`, opens its
    /// two existential execution witnesses, extracts its `starts` conjunct,
    /// specializes `no_start_fact` at that initial state, and derives a checked
    /// contradiction. All premises of `no_start_fact` remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem has the wrong conclusion, existential
    /// opening or universal specialization fails, or a checked propositional
    /// step is rejected. `kernel` is unchanged on failure.
    pub fn prove_never_calls_assert_from_no_start(
        self,
        kernel: &mut Kernel,
        program: Ref,
        assert_function: Ref,
        no_start_fact: ThmId,
    ) -> Result<Evidence, ReachabilityProofError> {
        let mut staged = kernel.fork();
        let no_start = self.no_admissible_start(&mut staged, program)?;
        let no_start_fact = align_positive_fact(&mut staged, no_start_fact, no_start)?;
        let calls = self.calls_assert(&mut staged, program, assert_function)?;
        let assumed_calls = staged.identity(positive(calls))?;

        let outer = open_exists(&mut staged, calls)?;
        let opened_outer = staged.copy_theorem(assumed_calls)?;
        staged.convert_conclusions(opened_outer, calls, outer.body)?;
        let inner = open_exists(&mut staged, outer.body)?;
        staged.convert_conclusions(opened_outer, outer.body, inner.body)?;
        let starts_fact =
            staged.expand_conclusion(opened_outer, positive(inner.body), Some(false))?;

        let denied = forall_elim(&mut staged, no_start_fact, outer.witness)
            .map_err(|source| ReachabilityProofError::Forall { source })?;
        let denied_fact =
            staged.flatten_conclusion(denied.theorem, positive(denied.proposition))?;
        let starts = apply2(&mut staged, self.starts, program, outer.witness)?;
        let denied_starts = staged
            .arena()
            .children(denied.proposition)
            .and_then(|mut children| children.next())
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "absence of admissible starts negation",
            })?;
        join_alpha_equivalent(&mut staged, denied_starts, starts)?;
        staged.convert_conclusions(denied_fact, denied_starts, starts)?;
        let starts_fact = align_positive_fact(&mut staged, starts_fact, starts)?;
        staged.not_left(starts_fact, positive(starts))?;
        let contradiction = staged.cut(denied_fact, starts_fact, positive(starts).negated())?;
        staged.not_right(contradiction, positive(calls))?;
        *kernel = staged;
        Ok(Evidence {
            proposition: calls,
            theorem: contradiction,
            holds: false,
        })
    }

    /// Proves `callsAssert` from one concrete checked execution witness.
    ///
    /// `starts_fact`, `steps_fact`, and `calls_fact` must respectively prove
    /// `starts program initial`, `steps initial final_state`, and
    /// `calls final_state assert_function`. Their premise matrices are
    /// preserved, allowing [`EvidenceScope`] to enforce the semantic boundary
    /// afterward. The result is converted to the canonical proposition emitted
    /// by [`calls_assert`](Self::calls_assert).
    ///
    /// # Errors
    ///
    /// Returns an error if a fact has the wrong conclusion, a witness has an
    /// incompatible classifier, existential introduction or alpha conversion
    /// fails, or any checked proof step is rejected. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_calls_assert(
        self,
        kernel: &mut Kernel,
        program: Ref,
        assert_function: Ref,
        initial: Ref,
        final_state: Ref,
        starts_fact: ThmId,
        steps_fact: ThmId,
        calls_fact: ThmId,
    ) -> Result<Evidence, ReachabilityProofError> {
        let mut staged = kernel.fork();
        let starts = apply2(&mut staged, self.starts, program, initial)?;
        let steps = apply2(&mut staged, self.steps, initial, final_state)?;
        let calls = apply2(&mut staged, self.calls, final_state, assert_function)?;
        let starts_fact = align_positive_fact(&mut staged, starts_fact, starts)?;
        let steps_fact = align_positive_fact(&mut staged, steps_fact, steps)?;
        let calls_fact = align_positive_fact(&mut staged, calls_fact, calls)?;
        let reached = staged.op2(Op2::And, steps, calls)?;
        let reached_fact = staged.and_right(steps_fact, calls_fact, positive(reached))?;
        let concrete_body = staged.op2(Op2::And, starts, reached)?;
        let concrete_fact = staged.and_right(starts_fact, reached_fact, positive(concrete_body))?;

        let roots = [
            self.program_ty,
            self.state_ty,
            self.bool_ty,
            self.starts,
            self.steps,
            self.calls,
            program,
            assert_function,
            initial,
            final_state,
        ];
        let initial_name = staged.fresh_name(&roots)?;
        let final_name = initial_name
            .checked_add(1)
            .ok_or(KernelError::TooManyNames)?;
        let initial_binder = staged.tm_fv(initial_name, self.state_ty)?;
        let final_binder = staged.tm_fv(final_name, self.state_ty)?;

        let steps_at_final = apply2(&mut staged, self.steps, initial, final_binder)?;
        let calls_at_final = apply2(&mut staged, self.calls, final_binder, assert_function)?;
        let reached_at_final = staged.op2(Op2::And, steps_at_final, calls_at_final)?;
        let body_at_final = staged.op2(Op2::And, starts, reached_at_final)?;
        let final_exists = introduce_exists(
            &mut staged,
            concrete_fact,
            final_binder,
            body_at_final,
            final_state,
        )?;

        let starts_at_initial = apply2(&mut staged, self.starts, program, initial_binder)?;
        let steps_at_binders = apply2(&mut staged, self.steps, initial_binder, final_binder)?;
        let reached_at_binders = staged.op2(Op2::And, steps_at_binders, calls_at_final)?;
        let body_at_binders = staged.op2(Op2::And, starts_at_initial, reached_at_binders)?;
        let final_exists_at_initial = staged.exists_tm(final_binder, body_at_binders)?;
        let outer = introduce_exists(
            &mut staged,
            final_exists.theorem,
            initial_binder,
            final_exists_at_initial,
            initial,
        )?;

        let canonical = self.calls_assert(&mut staged, program, assert_function)?;
        join_alpha_equivalent(&mut staged, outer.proposition, canonical)?;
        staged.convert_conclusions(outer.theorem, outer.proposition, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem: outer.theorem,
            holds: true,
        })
    }
}

/// Generic contextual observational equivalence.
///
/// A subject can be a complete Wasm module or one function definition. A
/// context is respectively a module environment or a well-formed module with
/// one function hole. `plug context subject` produces the closed object seen
/// by `observe`; `admissible` keeps ill-formed linking contexts out of the
/// quantification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContextualObservation {
    /// Classifier of modules or function definitions being compared.
    pub subject_ty: Ref,
    /// Classifier of enclosing contexts.
    pub context_ty: Ref,
    /// Classifier of closed objects accepted by the observation.
    pub observed_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Curried operation `context -> subject -> observed`.
    pub plug: Ref,
    /// Curried predicate `context -> subject -> bool`.
    pub admissible: Ref,
    /// Observation `observed -> bool`.
    pub observe: Ref,
}

impl ContextualObservation {
    /// Constructs contextual observational equivalence of two subjects.
    ///
    /// The result is
    /// `forall context. admissible context left /\ admissible context right ->
    /// observe (plug context left) = observe (plug context right)`.
    /// This is useful unchanged for whole programs and individual functions.
    ///
    /// # Errors
    ///
    /// Returns an error if any supplied operation has an incompatible type,
    /// quantification cannot allocate a fresh binder, or a checked constructor
    /// fails. `kernel` is unchanged on failure.
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        require_classifier(&mut staged, left, self.subject_ty)?;
        require_classifier(&mut staged, right, self.subject_ty)?;
        let context_name = staged.fresh_name(&[
            self.subject_ty,
            self.context_ty,
            self.observed_ty,
            self.bool_ty,
            self.plug,
            self.admissible,
            self.observe,
            left,
            right,
        ])?;
        let context = staged.tm_fv(context_name, self.context_ty)?;
        let proposition = self.at_context(&mut staged, context, left, right)?;
        let equivalent = staged.forall_tm(self.bool_ty, context, proposition)?;
        *kernel = staged;
        Ok(equivalent)
    }

    /// Constructs the observation-preservation obligation at one context.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible operands or a rejected checked HOL
    /// constructor.
    pub fn at_context(
        self,
        kernel: &mut Kernel,
        context: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        require_classifier(kernel, context, self.context_ty)?;
        require_classifier(kernel, left, self.subject_ty)?;
        require_classifier(kernel, right, self.subject_ty)?;
        let left_admissible = apply2(kernel, self.admissible, context, left)?;
        let right_admissible = apply2(kernel, self.admissible, context, right)?;
        let admissible = kernel.op2(Op2::And, left_admissible, right_admissible)?;
        let left_closed = apply2(kernel, self.plug, context, left)?;
        let right_closed = apply2(kernel, self.plug, context, right)?;
        require_classifier(kernel, left_closed, self.observed_ty)?;
        require_classifier(kernel, right_closed, self.observed_ty)?;
        let left_observation = kernel.app(self.observe, left_closed)?;
        let right_observation = kernel.app(self.observe, right_closed)?;
        require_bool(kernel, self.bool_ty, left_observation)?;
        require_bool(kernel, self.bool_ty, right_observation)?;
        let same = kernel.eq(self.bool_ty, left_observation, right_observation)?;
        kernel.op2(Op2::Imp, admissible, same)
    }

    /// Specializes checked contextual equivalence to one admissible context.
    ///
    /// For module definitions this is the per-closing-context elimination
    /// rule. Function equivalence below quantifies over replacement contexts
    /// whose results are related by this full module equivalence, so no
    /// separate context-composition assumption is needed.
    ///
    /// # Errors
    ///
    /// Returns an error unless all three input theorems have the exact required
    /// positive conclusions, or a checked specialization/propositional step
    /// fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_preservation(
        self,
        kernel: &mut Kernel,
        equivalence: ThmId,
        context: Ref,
        left: Ref,
        right: Ref,
        left_admissible: ThmId,
        right_admissible: ThmId,
    ) -> Result<Evidence, ObservationProofError> {
        let mut staged = kernel.fork();
        let specialized = forall_elim(&mut staged, equivalence, context)?;
        let expected = self.at_context(&mut staged, context, left, right)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, expected)?;
        let specialized_theorem = staged.copy_theorem(specialized.theorem)?;
        staged.convert_conclusions(specialized_theorem, specialized.proposition, expected)?;
        let implication_operands = staged
            .arena()
            .children(expected)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "contextual observation implication",
            })?
            .collect::<Vec<_>>();
        let [antecedent, same] = implication_operands.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual observation implication operands",
            }
            .into());
        };
        let admissibility_operands = staged
            .arena()
            .children(*antecedent)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "contextual observation admissibility conjunction",
            })?
            .collect::<Vec<_>>();
        let [left_ok, right_ok] = admissibility_operands.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual observation admissibility operands",
            }
            .into());
        };
        let left_fact = align_positive_fact(&mut staged, left_admissible, *left_ok)?;
        let right_fact = align_positive_fact(&mut staged, right_admissible, *right_ok)?;
        let antecedent_fact = staged.and_right(left_fact, right_fact, positive(*antecedent))?;
        let same_identity = staged.identity(positive(*same))?;
        let use_implication =
            staged.imp_left(antecedent_fact, same_identity, positive(expected))?;
        let theorem = staged.cut(specialized_theorem, use_implication, positive(expected))?;
        *kernel = staged;
        Ok(Evidence {
            proposition: *same,
            theorem,
            holds: true,
        })
    }

    /// Proves that one context distinguishes two subjects.
    ///
    /// The left observation must hold and the right observation must not hold;
    /// both subjects must be admissible in `context`. The result is checked
    /// negative evidence for contextual observational equivalence. Thus the
    /// method directly proves `TRUE` and `FALSE` distinct once their `SpecTec`
    /// reachability facts and an admissible identity context are available.
    ///
    /// # Errors
    ///
    /// Returns an error if any input theorem has the wrong signed conclusion,
    /// or specialization, equality transport, or classical refutation fails.
    /// `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_distinct(
        self,
        kernel: &mut Kernel,
        context: Ref,
        left: Ref,
        right: Ref,
        left_admissible: ThmId,
        right_admissible: ThmId,
        left_observed: ThmId,
        right_not_observed: ThmId,
    ) -> Result<Evidence, ObservationProofError> {
        let mut staged = kernel.fork();
        let equivalence = self.equivalent(&mut staged, left, right)?;
        let assumed_equivalence = staged.identity(positive(equivalence))?;
        let preservation = self.prove_preservation(
            &mut staged,
            assumed_equivalence,
            context,
            left,
            right,
            left_admissible,
            right_admissible,
        )?;
        let equality_children = staged
            .arena()
            .children(preservation.proposition)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "contextual observation equality",
            })?
            .collect::<Vec<_>>();
        let [_, left_observation, right_observation] = equality_children.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual observation equality operands",
            }
            .into());
        };
        let left_fact =
            align_observation_fact(&mut staged, left_observed, *left_observation, true)?;
        let right_negative =
            align_observation_fact(&mut staged, right_not_observed, *right_observation, false)?;
        let right_positive = staged.eq_mp(preservation.theorem, left_fact)?;
        staged.not_left(right_positive, positive(*right_observation))?;
        let contradiction = staged.cut(
            right_negative,
            right_positive,
            positive(*right_observation).negated(),
        )?;
        staged.not_right(contradiction, positive(equivalence))?;
        *kernel = staged;
        Ok(Evidence {
            proposition: equivalence,
            theorem: contradiction,
            holds: false,
        })
    }
}

/// Contextual equivalence for individual function definitions.
///
/// Function equivalence quantifies over a function-hole module context and,
/// inside it, every outer observation context used by module equivalence. This
/// formulation makes replacement congruence a direct universal-specialization
/// theorem rather than an unchecked assumption about context composition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FunctionObservation {
    /// Classifier of function definitions.
    pub function_ty: Ref,
    /// Classifier of modules containing one function hole.
    pub replacement_context_ty: Ref,
    /// Curried operation `replacement_context -> function -> module`.
    pub replace: Ref,
    /// Contextual observational equivalence of resulting modules.
    pub modules: ContextualObservation,
}

impl FunctionObservation {
    /// Constructs observational equivalence of two function definitions.
    ///
    /// The resulting proposition is
    /// `forall replacement. replace replacement left ≈module replace replacement right`.
    /// Since module equivalence itself quantifies over all admissible outer
    /// contexts, this is full contextual function equivalence.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible functions or replacement operation,
    /// fresh-name exhaustion, or a rejected checked constructor. `kernel` is
    /// unchanged on failure.
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        require_classifier(&mut staged, left, self.function_ty)?;
        require_classifier(&mut staged, right, self.function_ty)?;
        let name = staged.fresh_name(&[
            self.function_ty,
            self.replacement_context_ty,
            self.replace,
            left,
            right,
            self.modules.subject_ty,
            self.modules.context_ty,
            self.modules.observed_ty,
            self.modules.bool_ty,
            self.modules.plug,
            self.modules.admissible,
            self.modules.observe,
        ])?;
        let replacement = staged.tm_fv(name, self.replacement_context_ty)?;
        let left_module = apply2(&mut staged, self.replace, replacement, left)?;
        let right_module = apply2(&mut staged, self.replace, replacement, right)?;
        let module_equivalence = self
            .modules
            .equivalent(&mut staged, left_module, right_module)?;
        let equivalent = staged.forall_tm(self.modules.bool_ty, replacement, module_equivalence)?;
        *kernel = staged;
        Ok(equivalent)
    }

    /// Proves that replacing a function by an observationally equivalent one
    /// preserves module observational equivalence.
    ///
    /// The input theorem proves contextual function equivalence. The result is
    /// the module-equivalence theorem for the two modules obtained by plugging
    /// the functions into the selected replacement context. All input theorem
    /// premises remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem proves the exact function
    /// equivalence, universal specialization succeeds, and the resulting
    /// module-equivalence formula can be checked alpha-equivalent. `kernel` is
    /// unchanged on failure.
    pub fn prove_replacement_congruence(
        self,
        kernel: &mut Kernel,
        function_equivalence: ThmId,
        replacement: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, ObservationProofError> {
        let mut staged = kernel.fork();
        let expected_function_equivalence = self.equivalent(&mut staged, left, right)?;
        let source = sole_evidence_proposition(&staged, function_equivalence, true)?;
        join_alpha_equivalent(&mut staged, source, expected_function_equivalence)?;
        let aligned = staged.copy_theorem(function_equivalence)?;
        staged.convert_conclusions(aligned, source, expected_function_equivalence)?;
        let specialized = forall_elim(&mut staged, aligned, replacement)?;
        let left_module = apply2(&mut staged, self.replace, replacement, left)?;
        let right_module = apply2(&mut staged, self.replace, replacement, right)?;
        let module_equivalence = self
            .modules
            .equivalent(&mut staged, left_module, right_module)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, module_equivalence)?;
        let theorem = staged.copy_theorem(specialized.theorem)?;
        staged.convert_conclusions(theorem, specialized.proposition, module_equivalence)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: module_equivalence,
            theorem,
            holds: true,
        })
    }
}

fn align_observation_fact(
    kernel: &mut Kernel,
    theorem: ThmId,
    target: Ref,
    holds: bool,
) -> Result<ThmId, ObservationProofError> {
    let evidence = Evidence {
        proposition: target,
        theorem,
        holds,
    };
    if require_conclusion(kernel, evidence).is_ok() {
        return Ok(theorem);
    }
    let source = sole_evidence_proposition(kernel, theorem, holds)?;
    join_alpha_equivalent(kernel, source, target)?;
    let aligned = kernel.copy_theorem(theorem)?;
    kernel.convert_conclusions(aligned, source, target)?;
    require_conclusion(
        kernel,
        Evidence {
            proposition: target,
            theorem: aligned,
            holds,
        },
    )?;
    Ok(aligned)
}

fn sole_evidence_proposition(
    kernel: &Kernel,
    theorem: ThmId,
    holds: bool,
) -> Result<Ref, KernelError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "contextual observation unit conclusion",
        });
    };
    if conclusions.next().is_some() || literal.is_positive() != holds {
        return Err(KernelError::InvalidTheoremRule {
            rule: "contextual observation signed conclusion",
        });
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
        rule: "contextual observation conclusion reference",
    })
}

/// Why contextual observation preservation could not be proved.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum ObservationProofError {
    /// A checked HOL construction or theorem rule failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Equality-encoded universal specialization failed.
    #[snafu(display("could not specialize contextual equivalence: {source}"))]
    Forall {
        /// Underlying checked derived-rule failure.
        source: ForallError,
    },
    /// Checked formulas could not be aligned.
    #[snafu(display("could not align contextual observation formulas: {source}"))]
    Syntax {
        /// Underlying checked alpha-equivalence failure.
        source: SyntaxError,
    },
    /// An admissibility theorem did not prove the required positive fact.
    #[snafu(display("could not align an admissibility theorem: {source}"))]
    Reachability {
        /// Underlying checked fact-alignment failure.
        source: ReachabilityProofError,
    },
}

impl From<ForallError> for ObservationProofError {
    fn from(source: ForallError) -> Self {
        Self::Forall { source }
    }
}

impl From<SyntaxError> for ObservationProofError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

impl From<ReachabilityProofError> for ObservationProofError {
    fn from(source: ReachabilityProofError) -> Self {
        Self::Reachability { source }
    }
}

/// Why a concrete assertion-reachability witness could not be proved.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum ReachabilityProofError {
    /// A checked HOL construction or theorem rule failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Existential introduction failed.
    #[snafu(display("could not introduce an assertion-reachability witness: {source}"))]
    Exists {
        /// Underlying checked derived-rule failure.
        source: ExistsError,
    },
    /// Equality-encoded universal specialization failed.
    #[snafu(display("could not specialize absence of admissible starts: {source}"))]
    Forall {
        /// Underlying checked derived-rule failure.
        source: ForallError,
    },
    /// The proved existential could not be related to canonical syntax.
    #[snafu(display("could not canonicalize an assertion-reachability proof: {source}"))]
    Syntax {
        /// Underlying checked alpha-equivalence failure.
        source: SyntaxError,
    },
}

impl From<ExistsError> for ReachabilityProofError {
    fn from(source: ExistsError) -> Self {
        Self::Exists { source }
    }
}

impl From<SyntaxError> for ReachabilityProofError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

fn align_positive_fact(
    kernel: &mut Kernel,
    theorem: ThmId,
    target: Ref,
) -> Result<ThmId, ReachabilityProofError> {
    let source = {
        let theorem = kernel
            .thm()
            .get(theorem)
            .ok_or(KernelError::MissingTheorem { id: theorem })?;
        let mut conclusions = theorem.rhs.rows();
        let Some([literal]) = conclusions.next() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "assertion witness unit conclusion",
            }
            .into());
        };
        if conclusions.next().is_some() || !literal.is_positive() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "assertion witness positive conclusion",
            }
            .into());
        }
        Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
            rule: "assertion witness conclusion reference",
        })?
    };
    join_alpha_equivalent(kernel, source, target)?;
    let aligned = kernel.copy_theorem(theorem)?;
    kernel.convert_conclusions(aligned, source, target)?;
    Ok(aligned)
}

/// Concrete program and linker terms used to state the Boolean laws.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProgramConnectives {
    /// Classifier shared by program terms.
    pub program_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Predicate `program -> bool`.
    pub calls_assert: Ref,
    /// Concrete `TRUE` module term.
    pub true_program: Ref,
    /// Concrete `FALSE` module term.
    pub false_program: Ref,
    /// Concrete linker `program -> program -> program`.
    pub and_program: Ref,
    /// Concrete linker `program -> program -> program`.
    pub or_program: Ref,
}

/// Exact HOL propositions that a concrete Wasm program logic must prove.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProgramLogicObligations {
    /// `callsAssert(TRUE)`.
    pub true_calls: Ref,
    /// `not callsAssert(FALSE)`.
    pub false_never_calls: Ref,
    /// Universally closed OR linker equation.
    pub or_calls_iff: Ref,
    /// Universally closed AND linker equation.
    pub and_calls_iff: Ref,
}

impl ProgramConnectives {
    /// Constructs the four checked HOL goal terms for assertion program logic.
    ///
    /// This method only states the obligations. It neither assumes nor proves
    /// them, and therefore adds no theorem facts.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible module, linker, or predicate terms,
    /// name exhaustion, or a rejected checked HOL constructor. `kernel` is
    /// unchanged on failure.
    pub fn obligations(self, kernel: &mut Kernel) -> Result<ProgramLogicObligations, KernelError> {
        let mut staged = kernel.fork();
        let true_calls = staged.app(self.calls_assert, self.true_program)?;
        let false_calls = staged.app(self.calls_assert, self.false_program)?;
        let false_never_calls = staged.op1(Op1::Not, false_calls)?;
        let first = staged.fresh_name(&[
            self.program_ty,
            self.bool_ty,
            self.calls_assert,
            self.true_program,
            self.false_program,
            self.and_program,
            self.or_program,
        ])?;
        let second = first.checked_add(1).ok_or(KernelError::TooManyNames)?;
        let left = staged.tm_fv(first, self.program_ty)?;
        let right = staged.tm_fv(second, self.program_ty)?;
        let left_calls = staged.app(self.calls_assert, left)?;
        let right_calls = staged.app(self.calls_assert, right)?;
        let or_calls_iff = connective_law(
            &mut staged,
            self.bool_ty,
            self.calls_assert,
            self.or_program,
            Op2::Or,
            left,
            right,
        )?;
        let and_calls_iff = connective_law(
            &mut staged,
            self.bool_ty,
            self.calls_assert,
            self.and_program,
            Op2::And,
            left,
            right,
        )?;
        // Ensure both reused leaves are independently checked Boolean terms.
        require_bool(&mut staged, self.bool_ty, left_calls)?;
        require_bool(&mut staged, self.bool_ty, right_calls)?;
        *kernel = staged;
        Ok(ProgramLogicObligations {
            true_calls,
            false_never_calls,
            or_calls_iff,
            and_calls_iff,
        })
    }
}

fn connective_law(
    kernel: &mut Kernel,
    bool_ty: Ref,
    calls_assert: Ref,
    connective: Ref,
    operation: Op2,
    left: Ref,
    right: Ref,
) -> Result<Ref, KernelError> {
    let combined = apply2(kernel, connective, left, right)?;
    let combined_calls = kernel.app(calls_assert, combined)?;
    let left_calls = kernel.app(calls_assert, left)?;
    let right_calls = kernel.app(calls_assert, right)?;
    let expected = kernel.op2(operation, left_calls, right_calls)?;
    let equation = kernel.eq(bool_ty, combined_calls, expected)?;
    let equation = kernel.forall_tm(bool_ty, right, equation)?;
    kernel.forall_tm(bool_ty, left, equation)
}

fn apply2(kernel: &mut Kernel, function: Ref, left: Ref, right: Ref) -> Result<Ref, KernelError> {
    let applied = kernel.app(function, left)?;
    kernel.app(applied, right)
}

fn require_bool(kernel: &mut Kernel, bool_ty: Ref, proposition: Ref) -> Result<(), KernelError> {
    let classifier = kernel.classifier(proposition)?;
    if kernel.equivalent(classifier, bool_ty)? {
        Ok(())
    } else {
        Err(KernelError::ClassifierMismatch {
            expected: bool_ty,
            actual: classifier,
        })
    }
}

fn require_classifier(kernel: &mut Kernel, term: Ref, expected: Ref) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    if kernel.equivalent(actual, expected)? {
        Ok(())
    } else {
        Err(KernelError::InvalidTheoremRule {
            rule: "contextual observation classifier",
        })
    }
}

/// Immutable Boolean scaffolding for composing assertion propositions.
///
/// This is not a WebAssembly syntax or semantics. `Leaf` leaves room for a
/// separately grounded WebAssembly proposition; the four closed forms only
/// exercise propositional composition without consulting an evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssertCombinator<Leaf> {
    /// A proposition whose behavior must be supplied by a Wasm interpretation.
    Leaf(Leaf),
    /// A proposition that is false.
    False,
    /// A proposition that is true.
    True,
    /// Conjunction of two assertion propositions.
    And(Arc<Self>, Arc<Self>),
    /// Disjunction of two assertion propositions.
    Or(Arc<Self>, Arc<Self>),
}

impl<Leaf> AssertCombinator<Leaf> {
    /// Constructs a program leaf.
    pub const fn leaf(leaf: Leaf) -> Self {
        Self::Leaf(leaf)
    }

    /// Constructs the conjunction program without mutating either operand.
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self::And(Arc::new(self), Arc::new(other))
    }

    /// Constructs the disjunction program without mutating either operand.
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        Self::Or(Arc::new(self), Arc::new(other))
    }

    /// Derives the program's `CallsAssert` proposition by structural mapping.
    #[must_use]
    pub fn calls_assert(&self) -> Proposition<CallsAssert<Leaf>>
    where
        Leaf: Clone,
    {
        match self {
            Self::Leaf(program) => Proposition::atom(CallsAssert::new(program.clone())),
            Self::False => Proposition::False,
            Self::True => Proposition::True,
            Self::And(left, right) => left.calls_assert().and(right.calls_assert()),
            Self::Or(left, right) => left.calls_assert().or(right.calls_assert()),
        }
    }
}

impl<Program> CallsAssert<Program> {
    /// Constructs the conventional `assert` observation.
    #[must_use]
    pub fn new(program: Program) -> Self {
        Self {
            program,
            import: Symbol::new("assert"),
        }
    }

    /// Constructs an observation with an explicitly named import.
    #[must_use]
    pub fn named(program: Program, import: impl Into<Symbol>) -> Self {
        Self {
            program,
            import: import.into(),
        }
    }
}

/// A checked theorem deciding one closed proposition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Established {
    /// HOL term denoting the proposition.
    pub proposition: Ref,
    /// Kernel-owned theorem proving the proposition or its negation.
    pub theorem: ThmId,
    /// Whether the theorem proves the positive proposition.
    pub holds: bool,
}

/// Checked positive or negative evidence whose theorem premises remain visible.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Evidence {
    /// HOL term denoting the proposition.
    pub proposition: Ref,
    /// Kernel-owned theorem deriving the proposition or its negation.
    pub theorem: ThmId,
    /// Whether the theorem concludes the positive proposition.
    pub holds: bool,
}

/// Immutable allowlist for assumptions admitted by a semantic proof.
///
/// A checked theorem remains kernel authority; this scope additionally checks
/// that its premises are unit literals drawn from an explicit semantic theory
/// and grounding-law boundary. It cannot create theorem facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvidenceScope {
    allowed: Arc<[Lit]>,
}

impl EvidenceScope {
    /// Creates a scope containing positive semantic assumptions.
    #[must_use]
    pub fn positive(assumptions: &[Ref]) -> Self {
        Self {
            allowed: assumptions
                .iter()
                .map(|assumption| positive(*assumption))
                .collect(),
        }
    }

    /// Returns the exact allowed premise literals.
    #[must_use]
    pub fn allowed(&self) -> &[Lit] {
        &self.allowed
    }

    /// Checks evidence against this exact premise boundary.
    ///
    /// Unused assumptions are permitted. Every premise actually present in
    /// the theorem must be a unit literal in the allowlist, preventing an
    /// evaluator observation or the desired conclusion from being silently
    /// introduced as an extra premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem is absent, has the wrong conclusion, or
    /// contains a non-unit or unlisted premise.
    pub fn check(&self, kernel: &Kernel, evidence: Evidence) -> Result<Evidence, KernelError> {
        require_conclusion(kernel, evidence)?;
        let theorem =
            kernel
                .arena()
                .theorems()
                .get(evidence.theorem)
                .ok_or(KernelError::MissingTheorem {
                    id: evidence.theorem,
                })?;
        for row in theorem.lhs.rows() {
            let [premise] = row else {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "semantic evidence unit premise",
                });
            };
            let premise_ref = Ref::new(premise.magnitude().cast_signed()).ok_or(
                KernelError::InvalidTheoremRule {
                    rule: "semantic evidence premise reference",
                },
            )?;
            let mut admitted = false;
            for allowed in self.allowed.iter().copied() {
                if allowed.is_positive() != premise.is_positive() {
                    continue;
                }
                let allowed_ref = Ref::new(allowed.magnitude().cast_signed()).ok_or(
                    KernelError::InvalidTheoremRule {
                        rule: "semantic evidence allowed reference",
                    },
                )?;
                if kernel.equivalent(allowed_ref, premise_ref)? {
                    admitted = true;
                    break;
                }
            }
            if !admitted {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "semantic evidence premise allowlist",
                });
            }
        }
        Ok(evidence)
    }
}

impl From<Established> for Evidence {
    fn from(value: Established) -> Self {
        Self {
            proposition: value.proposition,
            theorem: value.theorem,
            holds: value.holds,
        }
    }
}

impl Proposition<Infallible> {
    /// Lowers and decides a closed formula using only checked HOL rules.
    ///
    /// No evaluator result or new axiom enters the theorem store. The theorem
    /// has no premises and concludes with `proposition` when `holds`, or its
    /// negative literal otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if a checked HOL construction fails.
    pub fn establish(&self, kernel: &mut Kernel, bool_ty: Ref) -> Result<Established, KernelError> {
        self.establish_with(kernel, bool_ty, &mut |atom, _, _| match *atom {})
    }
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn constant(kernel: &mut Kernel, bool_ty: Ref, value: bool) -> Result<Evidence, KernelError> {
    let proposition = kernel.bool(bool_ty, value)?;
    let conclusion = if value {
        positive(proposition)
    } else {
        positive(proposition).negated()
    };
    let theorem = kernel.true_right(conclusion)?;
    Ok(Evidence {
        proposition,
        theorem,
        holds: value,
    })
}

fn require_conclusion(kernel: &Kernel, evidence: Evidence) -> Result<(), KernelError> {
    let theorem =
        kernel
            .arena()
            .theorems()
            .get(evidence.theorem)
            .ok_or(KernelError::MissingTheorem {
                id: evidence.theorem,
            })?;
    let expected = if evidence.holds {
        positive(evidence.proposition)
    } else {
        positive(evidence.proposition).negated()
    };
    let mut rows = theorem.rhs.rows();
    if rows.next().is_none_or(|row| row != [expected]) || rows.next().is_some() {
        return Err(KernelError::InvalidTheoremRule {
            rule: "interpreted proposition conclusion",
        });
    }
    Ok(())
}

fn require_exact(kernel: &Kernel, established: Established) -> Result<(), KernelError> {
    let evidence = established.into();
    require_conclusion(kernel, evidence)?;
    require_premise_free(kernel, evidence).map(|_| ())
}

fn require_premise_free(kernel: &Kernel, evidence: Evidence) -> Result<Established, KernelError> {
    let theorem =
        kernel
            .arena()
            .theorems()
            .get(evidence.theorem)
            .ok_or(KernelError::MissingTheorem {
                id: evidence.theorem,
            })?;
    if theorem.lhs.rows().next().is_some() {
        return Err(KernelError::InvalidTheoremRule {
            rule: "premise-free interpreted proposition",
        });
    }
    Ok(Established {
        proposition: evidence.proposition,
        theorem: evidence.theorem,
        holds: evidence.holds,
    })
}

fn establish_and(
    kernel: &mut Kernel,
    left: Evidence,
    right: Evidence,
) -> Result<Evidence, KernelError> {
    let proposition = kernel.op2(Op2::And, left.proposition, right.proposition)?;
    let conjunction = positive(proposition);
    let theorem = if left.holds && right.holds {
        kernel.and_right(left.theorem, right.theorem, conjunction)?
    } else {
        let (false_side, other) = if left.holds {
            (right, left)
        } else {
            (left, right)
        };
        let working = kernel.copy_theorem(false_side.theorem)?;
        kernel.not_left(working, positive(false_side.proposition).negated())?;
        kernel.weaken(working, &[positive(other.proposition)], &[])?;
        let contradiction = kernel.and_left(working, conjunction)?;
        kernel.not_right(contradiction, conjunction)?;
        contradiction
    };
    Ok(Evidence {
        proposition,
        theorem,
        holds: left.holds && right.holds,
    })
}

fn establish_or(
    kernel: &mut Kernel,
    left: Evidence,
    right: Evidence,
) -> Result<Evidence, KernelError> {
    let proposition = kernel.op2(Op2::Or, left.proposition, right.proposition)?;
    let disjunction = positive(proposition);
    let theorem = if left.holds || right.holds {
        let (true_side, other) = if left.holds {
            (left, right)
        } else {
            (right, left)
        };
        let working = kernel.copy_theorem(true_side.theorem)?;
        kernel.weaken(working, &[], &[positive(other.proposition)])?;
        kernel.or_right(working, disjunction)?
    } else {
        let left_working = kernel.copy_theorem(left.theorem)?;
        let right_working = kernel.copy_theorem(right.theorem)?;
        kernel.not_left(left_working, positive(left.proposition).negated())?;
        kernel.not_left(right_working, positive(right.proposition).negated())?;
        let contradiction = kernel.or_left(left_working, right_working, disjunction)?;
        kernel.not_right(contradiction, disjunction)?;
        contradiction
    };
    Ok(Evidence {
        proposition,
        theorem,
        holds: left.holds || right.holds,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn establish(formula: &Proposition<Infallible>) -> (Kernel, Established) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let result = formula.establish(&mut kernel, bool_ty).unwrap();
        (kernel, result)
    }

    fn assert_exact(kernel: &Kernel, result: Established, expected: bool) {
        assert_eq!(result.holds, expected);
        let theorem = kernel.arena().theorems().get(result.theorem).unwrap();
        assert!(theorem.lhs.rows().next().is_none());
        let expected = if expected {
            positive(result.proposition)
        } else {
            positive(result.proposition).negated()
        };
        let rows = theorem.rhs.rows().collect::<Vec<_>>();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0], &[expected]);
    }

    #[test]
    fn true_and_false_produce_positive_and_negative_facts() {
        let (kernel, result) = establish(&Proposition::True);
        assert_exact(&kernel, result, true);
        let (kernel, result) = establish(&Proposition::False);
        assert_exact(&kernel, result, false);
    }

    #[test]
    fn and_and_or_have_their_boolean_meaning() {
        for (formula, expected) in [
            (Proposition::True.and(Proposition::True), true),
            (Proposition::True.and(Proposition::False), false),
            (Proposition::False.and(Proposition::True), false),
            (Proposition::False.and(Proposition::False), false),
            (Proposition::True.or(Proposition::True), true),
            (Proposition::True.or(Proposition::False), true),
            (Proposition::False.or(Proposition::True), true),
            (Proposition::False.or(Proposition::False), false),
        ] {
            let (kernel, result) = establish(&formula);
            assert_exact(&kernel, result, expected);
        }
    }

    #[test]
    fn calls_assert_is_generic_and_maps_immutably() {
        let formula = Proposition::atom(CallsAssert::new(Symbol::new("module-a"))).or(
            Proposition::atom(CallsAssert::named(Symbol::new("module-b"), "fail")),
        );
        let mapped = formula.map(&mut |atom| atom.program.clone());
        assert_eq!(
            mapped,
            Proposition::atom(Symbol::new("module-a"))
                .or(Proposition::atom(Symbol::new("module-b")))
        );
    }

    #[test]
    fn closed_program_examples_derive_checked_behavior() {
        for (program, expected) in [
            (AssertCombinator::True.and(AssertCombinator::False), false),
            (AssertCombinator::True.or(AssertCombinator::False), true),
        ] {
            let proposition: Proposition<CallsAssert<Infallible>> = program.calls_assert();
            let closed = proposition.map(&mut |atom| match atom.program {});
            let (kernel, result) = establish(&closed);
            assert_exact(&kernel, result, expected);
        }
    }

    #[test]
    fn checked_atom_evidence_is_reusable_compositionally() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let atom_evidence = constant(&mut kernel, bool_ty, true).unwrap();
        let atom = require_premise_free(&kernel, atom_evidence).unwrap();
        let formula = Proposition::atom("module").and(Proposition::atom("module"));

        let result = formula
            .establish_with(&mut kernel, bool_ty, &mut |_, _, _| Ok(atom))
            .unwrap();

        assert_exact(&kernel, atom, true);
        assert_exact(&kernel, result, true);
    }

    #[test]
    fn interpreted_atoms_require_exact_theorems() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let proposition = kernel.bool(bool_ty, true).unwrap();
        let theorem = kernel.identity(positive(proposition)).unwrap();
        let claimed = Established {
            proposition,
            theorem,
            holds: true,
        };

        let result =
            Proposition::atom("module")
                .establish_with(&mut kernel, bool_ty, &mut |_, _, _| Ok(claimed));

        assert!(matches!(
            result,
            Err(KernelError::InvalidTheoremRule {
                rule: "premise-free interpreted proposition"
            })
        ));
    }

    #[test]
    fn conditional_semantic_evidence_preserves_visible_premises() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let proposition = kernel.bool(bool_ty, true).unwrap();
        let theorem = kernel.identity(positive(proposition)).unwrap();
        let atom = Evidence {
            proposition,
            theorem,
            holds: true,
        };

        let result = Proposition::atom("module")
            .or(Proposition::False)
            .derive_with(&mut kernel, bool_ty, &mut |_, _, _| Ok(atom))
            .unwrap();

        let theorem = kernel.arena().theorems().get(result.theorem).unwrap();
        assert!(theorem.lhs.rows().next().is_some());
        assert!(result.holds);
    }

    #[test]
    fn semantic_scope_rejects_smuggled_goal_assumptions() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let theory = kernel.tm_fv(1, bool_ty).unwrap();
        let goal = kernel.tm_fv(2, bool_ty).unwrap();
        let scope = EvidenceScope::positive(&[theory]);

        let theory_evidence = Evidence {
            proposition: theory,
            theorem: kernel.identity(positive(theory)).unwrap(),
            holds: true,
        };
        assert_eq!(
            scope.check(&kernel, theory_evidence).unwrap(),
            theory_evidence
        );

        let smuggled = Evidence {
            proposition: goal,
            theorem: kernel.identity(positive(goal)).unwrap(),
            holds: true,
        };
        assert!(matches!(
            scope.check(&kernel, smuggled),
            Err(KernelError::InvalidTheoremRule {
                rule: "semantic evidence premise allowlist"
            })
        ));
    }

    #[test]
    fn calls_assert_is_checked_existential_reachability() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let program_ty = kernel.ty_fv(1, star).unwrap();
        let state_ty = kernel.ty_fv(2, star).unwrap();
        let function_ty = kernel.ty_fv(3, star).unwrap();
        let state_predicate = kernel.ty_arr(state_ty, bool_ty).unwrap();
        let starts_ty = kernel.ty_arr(program_ty, state_predicate).unwrap();
        let steps_ty = kernel.ty_arr(state_ty, state_predicate).unwrap();
        let function_predicate = kernel.ty_arr(function_ty, bool_ty).unwrap();
        let calls_ty = kernel.ty_arr(state_ty, function_predicate).unwrap();
        let starts = kernel.tm_fv(10, starts_ty).unwrap();
        let steps = kernel.tm_fv(11, steps_ty).unwrap();
        let calls = kernel.tm_fv(12, calls_ty).unwrap();
        let program = kernel.tm_fv(13, program_ty).unwrap();
        let assert_function = kernel.tm_fv(14, function_ty).unwrap();
        let initial = kernel.tm_fv(15, state_ty).unwrap();
        let final_state = kernel.tm_fv(16, state_ty).unwrap();
        let schema = AssertionReachability {
            program_ty,
            state_ty,
            bool_ty,
            starts,
            steps,
            calls,
        };

        let proposition = schema
            .calls_assert(&mut kernel, program, assert_function)
            .unwrap();
        let negative = schema
            .never_calls_assert(&mut kernel, program, assert_function)
            .unwrap();

        assert!(
            kernel
                .equivalent(kernel.classifier(proposition).unwrap(), bool_ty)
                .unwrap()
        );
        assert_eq!(kernel.classifier(negative).unwrap(), bool_ty);
        assert_ne!(negative, proposition);

        let starts_proposition = apply2(&mut kernel, starts, program, initial).unwrap();
        let steps_proposition = apply2(&mut kernel, steps, initial, final_state).unwrap();
        let calls_proposition = apply2(&mut kernel, calls, final_state, assert_function).unwrap();
        let starts_fact = kernel.identity(positive(starts_proposition)).unwrap();
        let steps_fact = kernel.identity(positive(steps_proposition)).unwrap();
        let calls_fact = kernel.identity(positive(calls_proposition)).unwrap();
        let evidence = schema
            .prove_calls_assert(
                &mut kernel,
                program,
                assert_function,
                initial,
                final_state,
                starts_fact,
                steps_fact,
                calls_fact,
            )
            .unwrap();
        EvidenceScope::positive(&[starts_proposition, steps_proposition, calls_proposition])
            .check(&kernel, evidence)
            .unwrap();
        join_alpha_equivalent(&mut kernel, evidence.proposition, proposition).unwrap();
        assert!(
            kernel
                .equivalent(evidence.proposition, proposition)
                .unwrap()
        );

        let before = kernel.arena().clone();
        assert!(
            schema
                .prove_calls_assert(
                    &mut kernel,
                    program,
                    assert_function,
                    initial,
                    final_state,
                    calls_fact,
                    steps_fact,
                    calls_fact,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(
            schema
                .calls_assert(&mut kernel, assert_function, program)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }

    #[test]
    fn no_admissible_start_proves_negative_assertion_reachability() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let binary_tail = kernel.ty_arr(value, bool_ty).unwrap();
        let binary_predicate = kernel.ty_arr(value, binary_tail).unwrap();
        let schema = AssertionReachability {
            program_ty: value,
            state_ty: value,
            bool_ty,
            starts: kernel.tm_fv(10, binary_predicate).unwrap(),
            steps: kernel.tm_fv(11, binary_predicate).unwrap(),
            calls: kernel.tm_fv(12, binary_predicate).unwrap(),
        };
        let program = kernel.tm_fv(13, value).unwrap();
        let assert_function = kernel.tm_fv(14, value).unwrap();
        let no_start = schema.no_admissible_start(&mut kernel, program).unwrap();
        let no_start_fact = kernel.identity(positive(no_start)).unwrap();

        let evidence = schema
            .prove_never_calls_assert_from_no_start(
                &mut kernel,
                program,
                assert_function,
                no_start_fact,
            )
            .unwrap();

        assert!(!evidence.holds);
        EvidenceScope::positive(&[no_start])
            .check(&kernel, evidence)
            .unwrap();
    }

    #[test]
    fn concrete_program_terms_generate_the_four_exact_proof_goals() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let program_ty = kernel.ty_fv(1, star).unwrap();
        let calls_ty = kernel.ty_arr(program_ty, bool_ty).unwrap();
        let linker_result_ty = kernel.ty_arr(program_ty, program_ty).unwrap();
        let linker_ty = kernel.ty_arr(program_ty, linker_result_ty).unwrap();
        let calls_assert = kernel.tm_fv(2, calls_ty).unwrap();
        let true_program = kernel.tm_fv(3, program_ty).unwrap();
        let false_program = kernel.tm_fv(4, program_ty).unwrap();
        let and_program = kernel.tm_fv(5, linker_ty).unwrap();
        let or_program = kernel.tm_fv(6, linker_ty).unwrap();
        let theorem_count = kernel.thm().live_theorems().count();

        let goals = ProgramConnectives {
            program_ty,
            bool_ty,
            calls_assert,
            true_program,
            false_program,
            and_program,
            or_program,
        }
        .obligations(&mut kernel)
        .unwrap();

        for proposition in [
            goals.true_calls,
            goals.false_never_calls,
            goals.or_calls_iff,
            goals.and_calls_iff,
        ] {
            assert_eq!(kernel.classifier(proposition).unwrap(), bool_ty);
        }
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
    }

    #[test]
    fn contextual_function_equivalence_proves_replacement_observation() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let function_ty = kernel.ty_fv(1, star).unwrap();
        let context_ty = kernel.ty_fv(2, star).unwrap();
        let module_ty = kernel.ty_fv(3, star).unwrap();
        let context_to_module = kernel.ty_arr(function_ty, module_ty).unwrap();
        let plug_ty = kernel.ty_arr(context_ty, context_to_module).unwrap();
        let context_to_bool = kernel.ty_arr(function_ty, bool_ty).unwrap();
        let admissible_ty = kernel.ty_arr(context_ty, context_to_bool).unwrap();
        let observe_ty = kernel.ty_arr(module_ty, bool_ty).unwrap();
        let plug = kernel.tm_fv(10, plug_ty).unwrap();
        let admissible = kernel.tm_fv(11, admissible_ty).unwrap();
        let observe = kernel.tm_fv(12, observe_ty).unwrap();
        let context = kernel.tm_fv(13, context_ty).unwrap();
        let left = kernel.tm_fv(14, function_ty).unwrap();
        let right = kernel.tm_fv(15, function_ty).unwrap();
        let schema = ContextualObservation {
            subject_ty: function_ty,
            context_ty,
            observed_ty: module_ty,
            bool_ty,
            plug,
            admissible,
            observe,
        };
        let equivalence = schema.equivalent(&mut kernel, left, right).unwrap();
        let equivalence_fact = kernel.identity(positive(equivalence)).unwrap();
        let left_ok = apply2(&mut kernel, admissible, context, left).unwrap();
        let right_ok = apply2(&mut kernel, admissible, context, right).unwrap();
        let left_ok_fact = kernel.identity(positive(left_ok)).unwrap();
        let right_ok_fact = kernel.identity(positive(right_ok)).unwrap();

        let preservation = schema
            .prove_preservation(
                &mut kernel,
                equivalence_fact,
                context,
                left,
                right,
                left_ok_fact,
                right_ok_fact,
            )
            .unwrap();

        EvidenceScope::positive(&[equivalence, left_ok, right_ok])
            .check(&kernel, preservation)
            .unwrap();
        assert_eq!(
            kernel.classifier(preservation.proposition).unwrap(),
            bool_ty
        );

        let left_module = apply2(&mut kernel, plug, context, left).unwrap();
        let right_module = apply2(&mut kernel, plug, context, right).unwrap();
        let left_observation = kernel.app(observe, left_module).unwrap();
        let right_observation = kernel.app(observe, right_module).unwrap();
        let left_observed = kernel.identity(positive(left_observation)).unwrap();
        let right_not_observed = kernel
            .identity(positive(right_observation).negated())
            .unwrap();
        let distinct = schema
            .prove_distinct(
                &mut kernel,
                context,
                left,
                right,
                left_ok_fact,
                right_ok_fact,
                left_observed,
                right_not_observed,
            )
            .unwrap();
        assert!(!distinct.holds);
        require_conclusion(&kernel, distinct).unwrap();
    }

    #[test]
    fn contextual_function_replacement_preserves_module_equivalence() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let function_ty = kernel.ty_fv(1, star).unwrap();
        let replacement_ty = kernel.ty_fv(2, star).unwrap();
        let module_ty = kernel.ty_fv(3, star).unwrap();
        let outer_ty = kernel.ty_fv(4, star).unwrap();
        let observed_ty = kernel.ty_fv(5, star).unwrap();
        let replace_tail = kernel.ty_arr(function_ty, module_ty).unwrap();
        let replace_ty = kernel.ty_arr(replacement_ty, replace_tail).unwrap();
        let plug_tail = kernel.ty_arr(module_ty, observed_ty).unwrap();
        let plug_ty = kernel.ty_arr(outer_ty, plug_tail).unwrap();
        let admissible_tail = kernel.ty_arr(module_ty, bool_ty).unwrap();
        let admissible_ty = kernel.ty_arr(outer_ty, admissible_tail).unwrap();
        let observation_predicate_ty = kernel.ty_arr(observed_ty, bool_ty).unwrap();
        let replace = kernel.tm_fv(10, replace_ty).unwrap();
        let plug = kernel.tm_fv(11, plug_ty).unwrap();
        let admissible = kernel.tm_fv(12, admissible_ty).unwrap();
        let observe = kernel.tm_fv(13, observation_predicate_ty).unwrap();
        let left = kernel.tm_fv(14, function_ty).unwrap();
        let right = kernel.tm_fv(15, function_ty).unwrap();
        let replacement = kernel.tm_fv(16, replacement_ty).unwrap();
        let functions = FunctionObservation {
            function_ty,
            replacement_context_ty: replacement_ty,
            replace,
            modules: ContextualObservation {
                subject_ty: module_ty,
                context_ty: outer_ty,
                observed_ty,
                bool_ty,
                plug,
                admissible,
                observe,
            },
        };
        let equivalence = functions.equivalent(&mut kernel, left, right).unwrap();
        let equivalence_fact = kernel.identity(positive(equivalence)).unwrap();

        let sound = functions
            .prove_replacement_congruence(
                &mut kernel,
                equivalence_fact,
                replacement,
                left,
                right,
            )
            .unwrap();

        EvidenceScope::positive(&[equivalence])
            .check(&kernel, sound)
            .unwrap();
        assert_eq!(kernel.classifier(sound.proposition).unwrap(), bool_ty);
    }
}
