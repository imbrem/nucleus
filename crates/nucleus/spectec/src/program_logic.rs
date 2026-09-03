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
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, ThmId,
    builtin::{Op1, Op2},
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
            .ok_or(KernelError::TooManyNames)?;
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
        let schema = AssertionReachability {
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

        let before = kernel.arena().clone();
        assert!(
            schema
                .calls_assert(&mut kernel, assert_function, program)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }
}
