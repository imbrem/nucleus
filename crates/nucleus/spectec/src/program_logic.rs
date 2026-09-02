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
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, ThmId, builtin::Op2};

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
}

/// An open atom saying a program can call a distinguished assertion import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallsAssert<Program> {
    /// Stable program identity chosen by the surrounding schema.
    pub program: Program,
    /// Imported function treated as the assertion observation.
    pub import: Symbol,
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
        match self {
            Self::Atom(atom) => match *atom {},
            Self::False => constant(kernel, bool_ty, false),
            Self::True => constant(kernel, bool_ty, true),
            Self::And(left, right) => {
                let left = left.establish(kernel, bool_ty)?;
                let right = right.establish(kernel, bool_ty)?;
                establish_and(kernel, left, right)
            }
            Self::Or(left, right) => {
                let left = left.establish(kernel, bool_ty)?;
                let right = right.establish(kernel, bool_ty)?;
                establish_or(kernel, left, right)
            }
        }
    }
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn constant(kernel: &mut Kernel, bool_ty: Ref, value: bool) -> Result<Established, KernelError> {
    let proposition = kernel.bool(bool_ty, value)?;
    let conclusion = if value {
        positive(proposition)
    } else {
        positive(proposition).negated()
    };
    let theorem = kernel.true_right(conclusion)?;
    Ok(Established {
        proposition,
        theorem,
        holds: value,
    })
}

fn establish_and(
    kernel: &mut Kernel,
    left: Established,
    right: Established,
) -> Result<Established, KernelError> {
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
        kernel.not_left(
            false_side.theorem,
            positive(false_side.proposition).negated(),
        )?;
        kernel.weaken(false_side.theorem, &[positive(other.proposition)], &[])?;
        let contradiction = kernel.and_left(false_side.theorem, conjunction)?;
        kernel.not_right(contradiction, conjunction)?;
        contradiction
    };
    Ok(Established {
        proposition,
        theorem,
        holds: left.holds && right.holds,
    })
}

fn establish_or(
    kernel: &mut Kernel,
    left: Established,
    right: Established,
) -> Result<Established, KernelError> {
    let proposition = kernel.op2(Op2::Or, left.proposition, right.proposition)?;
    let disjunction = positive(proposition);
    let theorem = if left.holds || right.holds {
        let (true_side, other) = if left.holds {
            (left, right)
        } else {
            (right, left)
        };
        kernel.weaken(true_side.theorem, &[], &[positive(other.proposition)])?;
        kernel.or_right(true_side.theorem, disjunction)?
    } else {
        kernel.not_left(left.theorem, positive(left.proposition).negated())?;
        kernel.not_left(right.theorem, positive(right.proposition).negated())?;
        let contradiction = kernel.or_left(left.theorem, right.theorem, disjunction)?;
        kernel.not_right(contradiction, disjunction)?;
        contradiction
    };
    Ok(Established {
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
}
