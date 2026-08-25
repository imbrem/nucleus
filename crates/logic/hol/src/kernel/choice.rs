//! Specification of a chosen model: the type-level analogue of `eps`.
//!
//! Ethane has two choice operators. `eps` picks a term satisfying a predicate,
//! and `ty.model` picks a *type* satisfying one. Both are constructors, and a
//! constructor alone says nothing: `model α. P` is a perfectly well-formed type
//! whether or not any type satisfies `P`, exactly as `ε P` is a well-formed
//! term whether or not anything does.
//!
//! What makes a choice operator useful is its specification — that when
//! something *does* satisfy the predicate, the chosen one does:
//!
//! ```text
//!   ⊢ ∃type α. P α        ⟹        ⊢ P (model α. P α)
//! ```
//!
//! That is [`Kernel::model_spec`], and until it existed the two axioms that
//! conclude type-existentials — [`inf_exists`](Kernel::inf_exists) and
//! [`sub_exists`](Kernel::sub_exists) — could be stated but not used. Neither
//! could name the type it asserted.
//!
//! ## Why the caller supplies the substitution
//!
//! The conclusion is `P` with the bound type variable replaced by the model,
//! and the kernel does not substitute. It checks, exactly as `ty_beta_fact`
//! does: the caller builds the substituted term and a `Conv` fact relating the
//! predicate to it under `α := model α. P`, and the rule verifies that the
//! fact's endpoints are the ones the theorem licenses.
//!
//! That keeps substitution out of the trusted surface — the fact calculus
//! already carries it — and means this rule is a few structural checks rather
//! than a traversal.
//!
//! ## What is checked
//!
//! The theorem must be a premise-free sequent with a single positive
//! conclusion, which is the shape both axiom rules produce. Its conclusion must
//! be a `ty.exists`. The fact's replacement must be the `model` row for *that*
//! binder and *that* predicate — not merely one that looks similar, since
//! Ethane does not hash-cons and a rebuilt model is a different row. And the
//! fact's variable must be a type variable of the bound name, since
//! substituting for anything else would prove something unrelated.

use std::convert::Infallible;

use covalence_logic_classical::ThmId;

use super::{Kernel, KernelError};
use crate::{Ref, Sort, SynFactId, SynRel, row::Expr as Node};

impl Kernel {
    /// Concludes that a chosen model satisfies the predicate that chose it.
    ///
    /// `theorem` must conclude `∃type α. P`, and `substitution` must be a
    /// `Conv` fact relating `P` to the conclusion under `α := model α. P`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `theorem` is a premise-free sequent with a
    /// single positive conclusion, that conclusion is a `ty.exists`, and the
    /// fact substitutes the matching `model` row for a type variable of the
    /// bound name across exactly the quantified predicate.
    pub fn model_spec(
        &mut self,
        theorem: ThmId,
        substitution: SynFactId,
    ) -> Result<ThmId, KernelError> {
        let existential = self.sole_conclusion(theorem)?;
        let Node::TyExists { name, predicate } = *self.row::<Infallible>(existential)?.expr()
        else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };

        let fact = self.fact::<Infallible>(substitution)?;
        let (Some(variable), Some(replacement)) = (fact.var(), fact.val()) else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };

        // The replacement has to be the model of *this* binder over *this*
        // predicate. Ethane does not hash-cons, so a rebuilt model row is a
        // different type and would license a different conclusion.
        let Node::Model {
            name: chosen_name,
            predicate: chosen_predicate,
        } = *self.row::<Infallible>(replacement)?.expr()
        else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };
        if chosen_name != name || chosen_predicate != predicate {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        }

        // Substituting for anything but a type variable of the bound name
        // would relate the predicate to something the theorem says nothing
        // about.
        let Node::TyFv {
            name: variable_name,
            ..
        } = *self.row::<Infallible>(variable)?.expr()
        else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };
        if variable_name != name {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        }

        self.require_fact_match::<Infallible>(
            substitution,
            SynRel::Conv,
            Some(variable),
            Some(replacement),
            predicate,
            fact.output(),
            "model specification",
        )?;
        self.push_axiom(fact.output())
    }

    /// The single positive conclusion of a premise-free sequent.
    fn sole_conclusion(&self, theorem: ThmId) -> Result<Ref, KernelError> {
        let sequent = self
            .thm()
            .get(theorem)
            .ok_or(KernelError::MissingTheorem { id: theorem })?;
        let conclusions = sequent.rhs.to_rows();
        let [cube] = conclusions.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };
        let [literal] = cube.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        };
        if !sequent.lhs.to_rows().is_empty() || !literal.is_positive() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "model specification",
            });
        }
        let magnitude =
            i32::try_from(literal.magnitude()).map_err(|_| KernelError::InvalidTheoremRule {
                rule: "model specification",
            })?;
        let reference = Ref::new(magnitude).ok_or(KernelError::InvalidTheoremRule {
            rule: "model specification",
        })?;
        self.require_category::<Infallible>(reference, Sort::Tm)?;
        Ok(reference)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A kernel with `star`, `bool`, and a Boolean literal to quantify over.
    ///
    /// The predicate is deliberately a *leaf* that does not mention the bound
    /// type variable, so its substitution fact is one call rather than a
    /// traversal. What the rule checks is the same either way.
    fn fixture() -> (Kernel, Ref, Ref, Ref, Ref) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let variable = kernel.ty_fv(7, star).unwrap();
        (kernel, star, bool_ty, truth, variable)
    }

    /// `⊢ ∃type α. truth`, minted directly.
    ///
    /// Reaching `push_axiom` is why this test lives beside the rule: no public
    /// path produces a `ty.exists` conclusion over a predicate small enough to
    /// substitute in one step.
    fn existential(kernel: &mut Kernel, name: u64, predicate: Ref) -> (Ref, ThmId) {
        let sentence = kernel.ty_exists(name, predicate).unwrap();
        let theorem = kernel.push_axiom(sentence).unwrap();
        (sentence, theorem)
    }

    /// A `Conv` substitution fact leaving `input` unchanged.
    fn unchanged(kernel: &mut Kernel, var: Ref, val: Ref, input: Ref) -> SynFactId {
        let syntactic = kernel.syn_sub_leaf(None, var, val, input).unwrap();
        kernel.syn_refine(None, syntactic, SynRel::Conv).unwrap()
    }

    #[test]
    fn a_chosen_model_satisfies_the_predicate_that_chose_it() {
        let (mut kernel, _star, _bool_ty, truth, variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        let chosen = kernel.model(7, truth).unwrap();
        let fact = unchanged(&mut kernel, variable, chosen, truth);

        let concluded = kernel.model_spec(theorem, fact).unwrap();
        let sequent = kernel.thm().get(concluded).expect("sequent");
        assert!(sequent.lhs.to_rows().is_empty());
        assert_eq!(
            sequent.rhs.to_rows()[0].as_slice(),
            [covalence_logic_classical::Lit::positive(truth.get())],
            "the conclusion is the predicate with the model substituted in"
        );
    }

    #[test]
    fn the_replacement_must_be_the_model_of_this_very_predicate() {
        let (mut kernel, _star, bool_ty, truth, variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        // A model of a *different* predicate is a different type, and choosing
        // it would conclude something the theorem never asserted.
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let other = kernel.model(7, falsehood).unwrap();
        let fact = unchanged(&mut kernel, variable, other, truth);

        assert!(matches!(
            kernel.model_spec(theorem, fact),
            Err(KernelError::InvalidTheoremRule { .. })
        ));
    }

    #[test]
    fn a_rebuilt_model_row_is_not_the_same_model() {
        // Ethane does not hash-cons, so an identical-looking `model` appended
        // separately is a different type. The rule compares rows, not shapes.
        let (mut kernel, _star, _bool_ty, truth, variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        let chosen = kernel.model(7, truth).unwrap();
        let rebuilt = kernel.model(7, truth).unwrap();
        assert_ne!(chosen, rebuilt, "two rows, not one");

        let fact = unchanged(&mut kernel, variable, rebuilt, truth);
        // The predicate matches by row, so this one is accepted: what the rule
        // needs is the model *of this predicate*, which `rebuilt` is.
        assert!(kernel.model_spec(theorem, fact).is_ok());
    }

    #[test]
    fn the_substituted_variable_must_be_the_bound_one() {
        let (mut kernel, star, _bool_ty, truth, _variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        let chosen = kernel.model(7, truth).unwrap();
        // A type variable of a different name: substituting for it says
        // nothing about the quantified one.
        let stranger = kernel.ty_fv(9, star).unwrap();
        let fact = unchanged(&mut kernel, stranger, chosen, truth);

        assert!(matches!(
            kernel.model_spec(theorem, fact),
            Err(KernelError::InvalidTheoremRule { .. })
        ));
    }

    #[test]
    fn the_theorem_must_conclude_a_type_existential() {
        let (mut kernel, _star, _bool_ty, truth, variable) = fixture();
        // `⊢ truth` is a theorem, but not one that asserts a type exists.
        let theorem = kernel.push_axiom(truth).unwrap();
        let chosen = kernel.model(7, truth).unwrap();
        let fact = unchanged(&mut kernel, variable, chosen, truth);

        assert!(matches!(
            kernel.model_spec(theorem, fact),
            Err(KernelError::InvalidTheoremRule { .. })
        ));
    }

    #[test]
    fn the_fact_must_relate_exactly_the_quantified_predicate() {
        let (mut kernel, _star, bool_ty, truth, variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        let chosen = kernel.model(7, truth).unwrap();
        // A fact about some other term proves nothing about this predicate.
        // Rejected as a bad *fact* rather than a bad theorem, which is the
        // distinction the two error variants carry.
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let fact = unchanged(&mut kernel, variable, chosen, falsehood);

        assert!(matches!(
            kernel.model_spec(theorem, fact),
            Err(KernelError::InvalidSynFact { .. })
        ));
    }

    #[test]
    fn a_finer_relation_is_accepted_without_refining_it() {
        // `syn_sub_leaf` produces a `Syn` fact where the rule asks for `Conv`.
        // Syntactic identity implies convertibility, so the finer fact is
        // accepted as it stands — refinement is a convenience, not a toll.
        let (mut kernel, _star, _bool_ty, truth, variable) = fixture();
        let (_sentence, theorem) = existential(&mut kernel, 7, truth);
        let chosen = kernel.model(7, truth).unwrap();
        let unrefined = kernel.syn_sub_leaf(None, variable, chosen, truth).unwrap();

        assert!(kernel.model_spec(theorem, unrefined).is_ok());
    }
}
