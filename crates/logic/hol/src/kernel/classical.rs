//! Checked finite classical sequents over stable local term references.

use covalence_logic_classical::{
    CheckedArena, ClassicalArena, ClassicalKernel as SyllogismKernel, Cnf, CnfId, Dnf, DnfId, Lit,
    LitVec, ThmId, ThmRef,
};
#[cfg(test)]
use covalence_logic_classical::{LitError, Refuter};

use super::{Kernel, KernelError, Node};
use crate::{
    Ref,
    builtin::{Op1, Op2},
};

#[derive(Clone)]
struct Thm(Cnf, Dnf);

impl Thm {
    const fn new(lhs: Cnf, rhs: Dnf) -> Self {
        Self(lhs, rhs)
    }
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn reference(proposition: Lit) -> Ref {
    Ref::new(i32::try_from(proposition.magnitude()).expect("literal magnitude fits i32"))
        .expect("literal magnitude is nonzero")
}

/// The exact theorem and syntax produced by equality reflexivity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReflThm {
    /// Object-language equality `term = term`.
    pub equality: Ref,
    /// Premise-free theorem concluding [`equality`](Self::equality).
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by Boolean deduction antisymmetry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AntisymmThm {
    /// Object-language Boolean equality between the two conclusions.
    pub equality: Ref,
    /// The theorem concluding [`equality`](Self::equality).
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by applying equal functions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApThm {
    /// Application of the equality's left-hand function.
    pub left: Ref,
    /// Application of the equality's right-hand function.
    pub right: Ref,
    /// Object-language equality between [`left`](Self::left) and
    /// [`right`](Self::right).
    pub equality: Ref,
    /// Premise-free theorem concluding [`equality`](Self::equality).
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by abstracting an equality.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AbsThm {
    /// Lambda abstraction of the equality's left operand.
    pub left: Ref,
    /// Lambda abstraction of the equality's right operand.
    pub right: Ref,
    /// Object-language equality between [`left`](Self::left) and
    /// [`right`](Self::right).
    pub equality: Ref,
    /// The theorem preserving the source premise matrix.
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by universal introduction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForallThm {
    /// Equality-encoded universal `∀ binder. body`.
    pub universal: Ref,
    /// Premise-free theorem concluding [`universal`](Self::universal).
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by premise-free type generalization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TyForallThm {
    /// Type-universal proposition `∀type name. predicate`.
    pub universal: Ref,
    /// Premise-free theorem concluding [`universal`](Self::universal).
    pub theorem: ThmId,
}

/// The exact theorem and syntax produced by Hilbert-choice introduction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ChoiceThm {
    /// The selected witness `ε predicate`.
    pub witness: Ref,
    /// The proposition `predicate (ε predicate)`.
    pub proposition: Ref,
    /// The theorem preserving the source premises and concluding
    /// [`proposition`](Self::proposition).
    pub theorem: ThmId,
}

/// The theorem and syntax produced by applying one function to equal terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApTerm {
    /// Application to the equality's left operand.
    pub left: Ref,
    /// Application to the equality's right operand.
    pub right: Ref,
    /// Equality between [`left`](Self::left) and [`right`](Self::right).
    pub equality: Ref,
    /// The theorem preserving the source premise matrix.
    pub theorem: ThmId,
}

impl Kernel {
    /// Borrows the universally valid syllogism arena.
    #[must_use]
    pub const fn syl(&self) -> &ClassicalArena {
        self.arena.syllogisms()
    }

    /// Opens the checked mutable syllogism arena.
    pub fn syl_mut(&mut self) -> CheckedArena<'_> {
        CheckedArena::new(self.arena.syllogisms_mut())
    }

    /// Borrows the HOL theorem arena.
    #[must_use]
    pub const fn thm(&self) -> &ClassicalArena {
        self.arena.theorems()
    }

    /// Opens the checked mutable HOL theorem arena.
    pub fn thm_mut(&mut self) -> CheckedArena<'_> {
        CheckedArena::new(self.arena.theorems_mut())
    }

    fn require_thm(&self, id: ThmId) -> Result<ThmRef<'_>, KernelError> {
        self.arena
            .theorems()
            .get(id)
            .ok_or(KernelError::MissingTheorem { id })
    }

    /// Imports a universal classical refutation and matches it to one canonical
    /// HOL AND-of-OR syntax tree.
    ///
    /// # Errors
    ///
    /// Returns an error unless `source` proves exactly the canonical CNF
    /// denoted by `formula` has an empty DNF conclusion.
    pub fn seal_cnf_refutation(
        &mut self,
        source: &SyllogismKernel,
        theorem: ThmId,
        formula: Lit,
    ) -> Result<ThmId, KernelError> {
        let theorem = source.get(theorem).ok_or(KernelError::InvalidTheoremRule {
            rule: "classical refutation import",
        })?;
        if theorem.rhs.rows().next().is_some() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "classical refutation conclusion",
            });
        }
        let mut expected = self.decode_cnf(formula)?;
        expected.normalize();
        let mut actual = theorem.lhs.to_owned();
        actual.normalize();
        if actual != expected {
            return Err(KernelError::InvalidTheoremRule {
                rule: "canonical CNF refutation match",
            });
        }
        self.push_sequent(&[formula], &[])
    }

    /// Introduces the identity sequent `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn identity(&mut self, p: Lit) -> Result<ThmId, KernelError> {
        self.push_sequent(&[p], &[p])
    }

    /// Weakens this theorem in place by adding propositions on either side.
    ///
    /// # Errors
    ///
    /// Returns an error for missing evidence or an invalid proposition.
    pub fn weaken(
        &mut self,
        theorem: ThmId,
        premises: &[Lit],
        conclusions: &[Lit],
    ) -> Result<(), KernelError> {
        let old = self.require_thm(theorem)?;
        let mut premises_out = old.lhs.to_rows();
        premises_out.extend(premises.iter().copied().map(unit_row));
        let mut conclusions_out = old.rhs.to_rows();
        conclusions_out.extend(conclusions.iter().copied().map(unit_row));
        self.validate_props(premises.iter().chain(conclusions.iter()).copied())?;
        let replacement = Thm::new(Cnf::new(premises_out), Dnf::new(conclusions_out));
        self.replace_theorem(theorem, replacement)
    }

    /// Weakens this theorem with complete CNF and DNF rows.
    ///
    /// Adding a clause strengthens the CNF antecedent. Adding a cube weakens
    /// the DNF consequent. Input order and duplicates are preserved after
    /// every proposition has been checked as a resident Boolean term.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing theorem or an invalid proposition. The
    /// theorem is unchanged on error.
    pub fn weaken_matrix(
        &mut self,
        theorem: ThmId,
        premises: &[LitVec],
        conclusions: &[LitVec],
    ) -> Result<(), KernelError> {
        self.require_thm(theorem)?;
        self.validate_props(
            premises
                .iter()
                .flat_map(|row| row.iter())
                .chain(conclusions.iter().flat_map(|row| row.iter()))
                .copied(),
        )?;
        let replacement = self.require_thm(theorem)?;
        let mut left = replacement.lhs.to_rows();
        left.extend_from_slice(premises);
        let mut right = replacement.rhs.to_rows();
        right.extend_from_slice(conclusions);
        self.replace_theorem(theorem, Thm::new(Cnf::new(left), Dnf::new(right)))
    }

    /// Replaces every signed occurrence of one Boolean atom in a theorem by
    /// a semantically equal Boolean atom, in place.
    ///
    /// Literal polarity is preserved.  This is the bridge from checked HOL
    /// conversion/equality columns to the physical atoms stored by the
    /// classical theorem matrix.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem exists, both references are
    /// checked Boolean terms, and they belong to the same semantic equality
    /// class.  Rejection leaves the theorem unchanged.
    pub fn convert_theorem(
        &mut self,
        theorem: ThmId,
        source: Ref,
        target: Ref,
    ) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(source)?;
        self.require_bool_term::<std::convert::Infallible>(target)?;
        if !self.equivalent(source, target)? {
            return Err(KernelError::InvalidTheoremRule {
                rule: "theorem conversion",
            });
        }
        let old = self.require_thm(theorem)?;
        let premises: Vec<LitVec> = old
            .lhs
            .rows()
            .map(|row| replace_atom(row, source, target))
            .collect();
        let conclusions: Vec<LitVec> = old
            .rhs
            .rows()
            .map(|row| replace_atom(row, source, target))
            .collect();
        self.replace_theorem(theorem, Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Replaces an atom only in a theorem's conclusion matrix.
    ///
    /// This is selective semantic rewriting: unlike
    /// [`convert_theorem`](Self::convert_theorem), an equal atom in the premise
    /// matrix is deliberately left untouched.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem exists and both checked Boolean
    /// rows belong to the same semantic equality class. Rejection leaves the
    /// theorem unchanged.
    pub fn convert_conclusions(
        &mut self,
        theorem: ThmId,
        source: Ref,
        target: Ref,
    ) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(source)?;
        self.require_bool_term::<std::convert::Infallible>(target)?;
        if !self.equivalent(source, target)? {
            return Err(KernelError::InvalidTheoremRule {
                rule: "theorem conclusion conversion",
            });
        }
        let old = self.require_thm(theorem)?;
        let premises = old.lhs.to_owned();
        let conclusions: Vec<LitVec> = old
            .rhs
            .rows()
            .map(|row| replace_atom(row, source, target))
            .collect();
        self.replace_theorem(theorem, Thm::new(premises, Dnf::new(conclusions)))
    }

    /// Introduces equality reflexivity (`REFL`).
    ///
    /// Constructs the object-language equality `term = term` and its exact
    /// premise-free theorem.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is the checked Boolean type and
    /// `term` is a checked term. Rejection is transactional.
    pub fn refl(&mut self, bool_ty: Ref, term: Ref) -> Result<ReflThm, KernelError> {
        self.require_bool_type::<std::convert::Infallible>(bool_ty)?;
        self.require_category::<std::convert::Infallible>(term, crate::Sort::Tm)?;
        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let equality = staged.eq(bool_ty, term, term)?;
        let theorem = staged.push_theorem(Thm::new(
            Cnf::default(),
            Dnf::new(vec![unit_row(positive(equality))]),
        ))?;
        *self = staged;
        Ok(ReflThm { equality, theorem })
    }

    /// Applies a proved function equality to one argument (`AP_THM`).
    ///
    /// If `theorem` is `Γ ⊢ f = g` with one conclusion, this constructs
    /// `f argument`, `g argument`, their object-language equality, and the
    /// theorem `Γ ⊢ f argument = g argument`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source theorem has exactly one positive
    /// conclusion, that conclusion is equality at an arrow type, and
    /// `argument` has the arrow domain. Rejection is transactional:
    /// neither syntax nor theorem slots are changed.
    pub fn ap_thm(&mut self, theorem: ThmId, argument: Ref) -> Result<ApThm, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        let premises = source_theorem.lhs.to_owned();
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(source)?;
        self.require_category::<std::convert::Infallible>(argument, crate::Sort::Tm)?;
        let Node::Eq(function_ty, function, varied) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "AP_THM equality conclusion",
            });
        };
        self.type_arrow_member::<std::convert::Infallible>(function_ty)?;

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let left = staged.app(function, argument)?;
        let right = staged.app(varied, argument)?;
        let equality = staged.eq(bool_ty, left, right)?;
        let theorem = staged.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(equality))]),
        ))?;
        *self = staged;
        Ok(ApThm {
            left,
            right,
            equality,
            theorem,
        })
    }

    /// Abstracts both sides of a proved equality (`ABS_THM`).
    ///
    /// From `Γ ⊢ l = r`, derives `Γ ⊢ (λbinder. l) = (λbinder. r)` when
    /// `binder` is absent from every proposition in `Γ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source has exactly one positive equality
    /// conclusion, `binder` is a checked term variable, and it is not free in
    /// any premise proposition. Rejection is transactional.
    pub fn abs_thm(&mut self, theorem: ThmId, binder: Ref) -> Result<AbsThm, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        let premises = source_theorem.lhs.to_owned();
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(source)?;
        self.require_form::<std::convert::Infallible>(binder, "tm.fv", |node| {
            matches!(node, Node::TmFv { .. })
        })?;
        let binder_ty = self.classifier(binder)?;
        let Node::Eq(_body_ty, left_body, right_body) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "ABS_THM equality conclusion",
            });
        };
        for literal in premises.rows().flat_map(|row| row.iter()).copied() {
            if self.contains_variable::<std::convert::Infallible>(reference(literal), binder)? {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "ABS_THM freshness",
                });
            }
        }

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let body_ty = staged.classifier(left_body)?;
        let right_body_ty = staged.classifier(right_body)?;
        if !staged.equivalent(body_ty, right_body_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: body_ty,
                actual: right_body_ty,
            });
        }
        let function_ty = staged.ty_arr(binder_ty, body_ty)?;
        let left = staged.lam_at(function_ty, binder, left_body)?;
        let right = staged.lam_at(function_ty, binder, right_body)?;
        let equality = staged.eq(bool_ty, left, right)?;
        let theorem = staged.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(equality))]),
        ))?;
        *self = staged;
        Ok(AbsThm {
            left,
            right,
            equality,
            theorem,
        })
    }

    /// Applies one checked function to both sides of a proved equality
    /// (`AP_TERM`).
    ///
    /// From `Γ ⊢ x = y`, derives `Γ ⊢ function x = function y`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source has exactly one positive equality
    /// conclusion and `function` accepts both operands. Rejection is
    /// transactional.
    pub fn ap_term(&mut self, theorem: ThmId, function: Ref) -> Result<ApTerm, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        let premises = source_theorem.lhs.to_owned();
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(source)?;
        let Node::Eq(_, left_operand, right_operand) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "AP_TERM equality conclusion",
            });
        };

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let left = staged.app(function, left_operand)?;
        let right = staged.app(function, right_operand)?;
        let equality = staged.eq(bool_ty, left, right)?;
        let theorem = staged.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(equality))]),
        ))?;
        *self = staged;
        Ok(ApTerm {
            left,
            right,
            equality,
            theorem,
        })
    }

    /// Rewrites a proved proposition through a proved Boolean equality
    /// (`EQ_MP`).
    ///
    /// From `Γ ⊢ p = q` and `Π ⊢ p`, derives `Γ, Π ⊢ q`.
    ///
    /// # Errors
    ///
    /// Returns an error unless each source has exactly one positive
    /// conclusion and those conclusions have the displayed exact shape.
    pub fn eq_mp(
        &mut self,
        equality_theorem: ThmId,
        premise_theorem: ThmId,
    ) -> Result<ThmId, KernelError> {
        let equality_source = self.require_thm(equality_theorem)?;
        let equality = sole_positive_conclusion(equality_source)?;
        let premise_source = self.require_thm(premise_theorem)?;
        let premise = sole_positive_conclusion(premise_source)?;
        self.require_bool_term::<std::convert::Infallible>(equality)?;
        let Node::Eq(ty, left, right) = *self.row(equality)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "EQ_MP equality conclusion",
            });
        };
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(left)?;
        self.require_bool_term::<std::convert::Infallible>(right)?;
        if ty != bool_ty || premise != left {
            return Err(KernelError::InvalidTheoremRule {
                rule: "EQ_MP proposition match",
            });
        }
        let mut premises = equality_source.lhs.to_rows();
        premises.extend(premise_source.lhs.to_rows());
        self.push_theorem(Thm::new(
            Cnf::new(premises),
            Dnf::new(vec![unit_row(positive(right))]),
        ))
    }

    /// Eliminates equality with truth (`EQT_ELIM`).
    ///
    /// If `theorem` is `Γ ⊢ p = true` with one conclusion, this allocates
    /// `Γ ⊢ p`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source has one positive equality conclusion
    /// whose right operand is the Boolean truth literal.
    /// Rejection does not alter theorem storage.
    pub fn eqt_elim(&mut self, theorem: ThmId) -> Result<ThmId, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        let premises = source_theorem.lhs.to_owned();
        self.require_bool_term::<std::convert::Infallible>(source)?;
        let Node::Eq(_, proposition, truth) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "EQT_ELIM equality conclusion",
            });
        };
        self.require_bool_term::<std::convert::Infallible>(proposition)?;
        if self.arena.bool_value(truth) != Some(true) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "EQT_ELIM truth operand",
            });
        }
        self.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(proposition))]),
        ))
    }

    /// Introduces Boolean equality from mutual entailment (`DEDUCT_ANTISYM`).
    ///
    /// If `left` proves `q` under a possible unit premise `p`, and `right`
    /// proves `p` under a possible unit premise `q`, this discharges those
    /// premises and concludes `p = q`. A missing premise is accepted because
    /// it represents the stronger, premise-independent theorem.
    ///
    /// # Errors
    ///
    /// Returns an error unless both sources have one positive Boolean
    /// conclusion and `bool_ty` is the checked Boolean type. Rejection is
    /// transactional.
    pub fn deduct_antisym(
        &mut self,
        bool_ty: Ref,
        p: Ref,
        q: Ref,
        left: ThmId,
        right: ThmId,
    ) -> Result<AntisymmThm, KernelError> {
        self.require_bool_type::<std::convert::Infallible>(bool_ty)?;
        self.require_bool_term::<std::convert::Infallible>(p)?;
        self.require_bool_term::<std::convert::Infallible>(q)?;
        let left_source = self.require_thm(left)?;
        if !sole_positive_conclusion(left_source).is_ok_and(|actual| actual == q) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "DEDUCT_ANTISYM left conclusion",
            });
        }
        let mut left_premises = left_source.lhs.to_rows();
        let right_source = self.require_thm(right)?;
        if !sole_positive_conclusion(right_source).is_ok_and(|actual| actual == p) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "DEDUCT_ANTISYM right conclusion",
            });
        }
        let mut right_premises = right_source.lhs.to_rows();
        remove_unit_row(&mut left_premises, positive(p), LitVec::as_slice);
        remove_unit_row(&mut right_premises, positive(q), LitVec::as_slice);

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let equality = staged.eq(bool_ty, p, q)?;
        left_premises.extend(right_premises);
        let theorem = staged.push_theorem(Thm::new(
            Cnf::new(left_premises),
            Dnf::new(vec![unit_row(positive(equality))]),
        ))?;
        *self = staged;
        Ok(AntisymmThm { equality, theorem })
    }

    /// Introduces Hilbert choice from one proved witness.
    ///
    /// From `Γ ⊢ predicate argument`, derives
    /// `Γ ⊢ predicate (ε predicate)`. This is HOL's standard choice rule; the
    /// chosen witness itself carries no additional assumption.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source has exactly one positive conclusion
    /// of application form. Rejection is transactional.
    pub fn choice_intro(&mut self, theorem: ThmId) -> Result<ChoiceThm, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        self.require_bool_term::<std::convert::Infallible>(source)?;
        let Node::App(predicate, _) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "choice introduction application",
            });
        };
        let predicate_ty = self.classifier(predicate)?;
        let (domain, _) = self.type_arrow_member::<std::convert::Infallible>(predicate_ty)?;

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let witness = staged.eps(domain, predicate)?;
        let proposition = staged.app(predicate, witness)?;
        let theorem = staged.choice_intro_at(theorem, proposition)?;
        *self = staged;
        Ok(ChoiceThm {
            witness,
            proposition,
            theorem,
        })
    }

    /// Introduces choice into an existing checked target application.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem has sole conclusion `predicate x`
    /// and `target` is exactly `predicate (ε predicate)`.
    pub fn choice_intro_at(&mut self, theorem: ThmId, target: Ref) -> Result<ThmId, KernelError> {
        let source_theorem = self.require_thm(theorem)?;
        let source = sole_positive_conclusion(source_theorem)?;
        let premises = source_theorem.lhs.to_owned();
        self.require_bool_term::<std::convert::Infallible>(source)?;
        self.require_bool_term::<std::convert::Infallible>(target)?;
        let Node::App(predicate, _) = *self.row(source)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "choice introduction application",
            });
        };
        let Node::App(target_predicate, witness) = *self.row(target)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "choice introduction target application",
            });
        };
        let Node::Eps {
            predicate: selected,
            ..
        } = *self.row(witness)?.expr()
        else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "choice introduction target witness",
            });
        };
        if target_predicate != predicate || selected != predicate {
            return Err(KernelError::InvalidTheoremRule {
                rule: "choice introduction target predicate",
            });
        }
        self.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(target))]),
        ))
    }

    /// Universally generalizes one theorem (`GEN`).
    ///
    /// If `theorem` is `Γ ⊢ body`, this constructs the standard
    /// equality-encoded `∀ binder. body` and `Γ ⊢ ∀ binder. body`, provided
    /// the binder is not free in any proposition in `Γ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source has exactly one positive Boolean
    /// conclusion, `binder` is a checked term variable, and `binder` is absent
    /// from every premise proposition. Rejection is transactional.
    pub fn forall_intro(&mut self, theorem: ThmId, binder: Ref) -> Result<ForallThm, KernelError> {
        let body = sole_positive_conclusion(self.require_thm(theorem)?)?;
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(body)?;

        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let universal = staged.forall_tm(bool_ty, binder, body)?;
        let theorem = staged.forall_intro_at(theorem, binder, universal)?;
        *self = staged;
        Ok(ForallThm { universal, theorem })
    }

    /// Generalizes into an existing equality-encoded universal row.
    ///
    /// This is the allocation-free target form of [`forall_intro`](Self::forall_intro),
    /// useful when an untrusted elaborator has already constructed the exact
    /// statement it wants to prove.
    ///
    /// # Errors
    ///
    /// Returns an error unless `theorem` is `Γ ⊢ body`, `binder` is absent
    /// from every proposition in `Γ`, and `universal` is exactly
    /// `∀ binder. body` in the standard checked encoding.
    pub fn forall_intro_at(
        &mut self,
        theorem: ThmId,
        binder: Ref,
        universal: Ref,
    ) -> Result<ThmId, KernelError> {
        let source = self.require_thm(theorem)?;
        let body = sole_positive_conclusion(source)?;
        let premises = source.lhs.to_owned();
        let bool_ty = self.require_bool_term::<std::convert::Infallible>(body)?;
        self.require_form::<std::convert::Infallible>(binder, "tm.fv", |node| {
            matches!(node, Node::TmFv { .. })
        })?;
        for literal in premises.rows().flat_map(|row| row.iter()).copied() {
            if self.contains_variable::<std::convert::Infallible>(reference(literal), binder)? {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "universal introduction freshness",
                });
            }
        }
        if self.require_bool_term::<std::convert::Infallible>(universal)? != bool_ty {
            return Err(KernelError::InvalidTheoremRule {
                rule: "universal introduction Boolean type",
            });
        }
        let Node::Eq(_, left, right) = *self.row(universal)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "universal introduction target",
            });
        };
        let Node::Lam(left_binder, left_body) = *self.row(left)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "universal introduction predicate",
            });
        };
        let Node::Lam(right_binder, right_body) = *self.row(right)?.expr() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "universal introduction truth function",
            });
        };
        if left_binder != binder
            || right_binder != binder
            || left_body != body
            || self.arena.bool_value(right_body) != Some(true)
        {
            return Err(KernelError::InvalidTheoremRule {
                rule: "universal introduction target",
            });
        }
        self.push_theorem(Thm::new(
            premises,
            Dnf::new(vec![unit_row(positive(universal))]),
        ))
    }

    /// Universally generalizes a premise-free theorem over one named type.
    ///
    /// This deliberately narrow rule accepts only `[] ⊢ predicate`. The source
    /// derivation is therefore uniform in the free type named by `name`, and
    /// the result is exactly `[] ⊢ ty.forall name predicate`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `theorem` exists and has no premises and exactly
    /// one positive Boolean conclusion. Rejection is transactional.
    pub fn ty_forall_intro(
        &mut self,
        theorem: ThmId,
        name: u64,
    ) -> Result<TyForallThm, KernelError> {
        let source = self.require_thm(theorem)?;
        if source.lhs.rows().next().is_some() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "type universal introduction",
            });
        }
        let predicate = sole_positive_conclusion(source)?;
        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let universal = staged.ty_forall(name, predicate)?;
        let theorem = staged.push_theorem(Thm::new(
            Cnf::default(),
            Dnf::new(vec![unit_row(positive(universal))]),
        ))?;
        *self = staged;
        Ok(TyForallThm { universal, theorem })
    }

    /// Moves one indexed CNF row to the right with pointwise-negated literals.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or clause is absent. The theorem is
    /// unchanged on error.
    pub fn move_cnf_right(&mut self, theorem: ThmId, row: CnfId) -> Result<(), KernelError> {
        self.arena
            .theorems_mut()
            .move_cnf_right(theorem, row)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "CNF transfer right",
            })
    }

    /// Moves one indexed DNF row to the left with pointwise-negated literals.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or cube is absent. The theorem is
    /// unchanged on error.
    pub fn move_dnf_left(&mut self, theorem: ThmId, row: DnfId) -> Result<(), KernelError> {
        self.arena
            .theorems_mut()
            .move_dnf_left(theorem, row)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "DNF transfer left",
            })
    }

    /// Canonicalizes one indexed CNF row in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or clause is absent.
    pub fn normalize_cnf(&mut self, theorem: ThmId, row: CnfId) -> Result<(), KernelError> {
        self.arena
            .theorems_mut()
            .normalize_cnf(theorem, row)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "CNF row normalization",
            })
    }

    /// Canonicalizes one indexed DNF row in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or cube is absent.
    pub fn normalize_dnf(&mut self, theorem: ThmId, row: DnfId) -> Result<(), KernelError> {
        self.arena
            .theorems_mut()
            .normalize_dnf(theorem, row)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "DNF row normalization",
            })
    }

    /// Contracts and canonicalizes both matrices of one theorem in place.
    ///
    /// This removes duplicate rows and duplicate literals as a sound
    /// structural mutation. It is useful after multi-premise Gentzen rules
    /// concatenate contexts that share assumptions.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem handle is absent.
    pub fn contract_theorem(&mut self, theorem: ThmId) -> Result<(), KernelError> {
        let source = self.require_thm(theorem)?;
        let mut premises = source.lhs.to_owned();
        let mut conclusions = source.rhs.to_owned();
        premises.normalize();
        conclusions.normalize();
        self.replace_theorem(theorem, Thm::new(premises, conclusions))
    }

    /// Cuts a proposition occurring on opposite sides of two sequents.
    ///
    /// From `Γ |- Δ, p` and `p, Π |- Λ`, derives `Γ, Π |- Δ, Λ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorem handles exist and `p` occurs in
    /// the required conclusion and premise.
    pub fn cut(
        &mut self,
        left: ThmId,
        right: ThmId,
        proposition: Lit,
    ) -> Result<ThmId, KernelError> {
        let lhs = self.require_thm(left)?;
        let rhs = self.require_thm(right)?;
        let mut left_conclusions = lhs.rhs.to_rows();
        let mut right_premises = rhs.lhs.to_rows();
        if !remove_unit_row(&mut left_conclusions, proposition, LitVec::as_slice)
            || !remove_unit_row(&mut right_premises, proposition, LitVec::as_slice)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "cut" });
        }
        let mut premises = lhs.lhs.to_rows();
        premises.extend(right_premises);
        let mut conclusions = left_conclusions;
        conclusions.extend(rhs.rhs.to_rows());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Introduces falsity on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless `falsehood` is a signed Boolean literal whose
    /// checked constant value is false.
    pub fn false_left(&mut self, falsehood: Lit) -> Result<ThmId, KernelError> {
        if self.signed_bool_value(falsehood)? != Some(false) {
            return Err(KernelError::InvalidTheoremRule { rule: "false left" });
        }
        self.push_sequent(&[falsehood], &[])
    }

    /// Records `conclusion` as a premise-free theorem.
    ///
    /// Visible to sibling kernel modules only, and deliberately narrower than
    /// [`push_sequent`](Self::push_sequent): an axiom rule needs to conclude
    /// one proposition and nothing else. **Nothing here checks that the
    /// conclusion is warranted** — the caller is the rule that justified it,
    /// which is why this must never be reachable from outside the kernel.
    ///
    /// # Errors
    ///
    /// Returns an error unless `conclusion` is a checked Boolean term, or if
    /// the theorem arena is full.
    pub(super) fn push_axiom(&mut self, conclusion: Ref) -> Result<ThmId, KernelError> {
        self.require_bool_term::<std::convert::Infallible>(conclusion)?;
        self.push_sequent(&[], &[positive(conclusion)])
    }

    /// Introduces truth on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless `truth` is a signed Boolean literal whose
    /// checked constant value is true.
    pub fn true_right(&mut self, truth: Lit) -> Result<ThmId, KernelError> {
        if self.signed_bool_value(truth)? != Some(true) {
            return Err(KernelError::InvalidTheoremRule { rule: "true right" });
        }
        self.push_sequent(&[], &[truth])
    }

    /// Moves a conclusion to the left with complementary polarity in place.
    ///
    /// From `Γ |- Δ, p`, derives `¬p, Γ |- Δ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the conclusion.
    pub fn not_left(&mut self, theorem: ThmId, p: Lit) -> Result<(), KernelError> {
        let source = self.require_thm(theorem)?;
        let mut conclusions = source.rhs.to_rows();
        if !remove_unit(&mut conclusions, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not left" });
        }
        let mut premises = source.lhs.to_rows();
        premises.push(unit_row(p.negated()));
        let replacement = Thm::new(Cnf::new(premises), Dnf::new(conclusions));
        self.replace_theorem(theorem, replacement)
    }

    /// Moves a premise to the right with complementary polarity in place.
    ///
    /// From `p, Γ |- Δ`, derives `Γ |- Δ, ¬p`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the premise.
    pub fn not_right(&mut self, theorem: ThmId, p: Lit) -> Result<(), KernelError> {
        let source = self.require_thm(theorem)?;
        let mut premises = source.lhs.to_rows();
        if !remove_unit(&mut premises, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not right" });
        }
        let mut conclusions = source.rhs.to_rows();
        conclusions.push(unit_row(p.negated()));
        let replacement = Thm::new(Cnf::new(premises), Dnf::new(conclusions));
        self.replace_theorem(theorem, replacement)
    }

    /// Folds two conjunct premises into their checked conjunction opcode.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands occur in the premise and
    /// `conjunction` is their positive `tm.and` opcode.
    pub fn and_left(&mut self, theorem: ThmId, conjunction: Lit) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(conjunction, Op2::And)?;
        let source = self.require_thm(theorem)?;
        let mut premises = source.lhs.to_rows();
        if !remove_unit_pair(&mut premises, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and left" });
        }
        premises.push(unit_row(conjunction));
        self.push_theorem(Thm::new(Cnf::new(premises), source.rhs.to_owned()))
    }

    /// Introduces a checked conjunction on the right, concatenating contexts.
    ///
    /// # Errors
    ///
    /// Returns an error unless the left and right operand conclusions occur.
    pub fn and_right(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        conjunction: Lit,
    ) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(conjunction, Op2::And)?;
        let lhs = self.require_thm(left_theorem)?;
        let rhs = self.require_thm(right_theorem)?;
        let mut left_conc = lhs.rhs.to_rows();
        let mut right_conc = rhs.rhs.to_rows();
        if !remove_unit(&mut left_conc, left) || !remove_unit(&mut right_conc, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and right" });
        }
        let mut premises = lhs.lhs.to_rows();
        premises.extend(rhs.lhs.to_rows());
        let mut conclusions = left_conc;
        conclusions.extend(right_conc);
        conclusions.push(unit_row(conjunction));
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Introduces a checked disjunction on the left, concatenating contexts.
    ///
    /// # Errors
    ///
    /// Returns an error unless the operand premises occur.
    pub fn or_left(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        disjunction: Lit,
    ) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(disjunction, Op2::Or)?;
        let lhs = self.require_thm(left_theorem)?;
        let rhs = self.require_thm(right_theorem)?;
        let mut left_prem = lhs.lhs.to_rows();
        let mut right_prem = rhs.lhs.to_rows();
        if !remove_unit(&mut left_prem, left) || !remove_unit(&mut right_prem, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or left" });
        }
        let mut premises = left_prem;
        premises.extend(right_prem);
        premises.push(unit_row(disjunction));
        let mut conclusions = lhs.rhs.to_rows();
        conclusions.extend(rhs.rhs.to_rows());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Folds two conclusions into their checked disjunction opcode.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands occur in the conclusion and
    /// `disjunction` is their positive `tm.or` opcode.
    pub fn or_right(&mut self, theorem: ThmId, disjunction: Lit) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(disjunction, Op2::Or)?;
        let source = self.require_thm(theorem)?;
        let mut conclusions = source.rhs.to_rows();
        if !remove_unit_pair(&mut conclusions, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or right" });
        }
        conclusions.push(unit_row(disjunction));
        self.push_theorem(Thm::new(source.lhs.to_owned(), Dnf::new(conclusions)))
    }

    /// Introduces a checked implication on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless the antecedent is a conclusion of `left` and
    /// the consequent is a premise of `right`.
    pub fn imp_left(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        implication: Lit,
    ) -> Result<ThmId, KernelError> {
        let (antecedent, consequent) = self.require_binary(implication, Op2::Imp)?;
        let lhs = self.require_thm(left_theorem)?;
        let rhs = self.require_thm(right_theorem)?;
        let mut left_conc = lhs.rhs.to_rows();
        let mut right_prem = rhs.lhs.to_rows();
        if !remove_unit(&mut left_conc, antecedent) || !remove_unit(&mut right_prem, consequent) {
            return Err(KernelError::InvalidTheoremRule { rule: "imp left" });
        }
        let mut premises = lhs.lhs.to_rows();
        premises.extend(right_prem);
        premises.push(unit_row(implication));
        let mut conclusions = left_conc;
        conclusions.extend(rhs.rhs.to_rows());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Introduces a checked implication on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless the antecedent occurs in the premise and the
    /// consequent occurs in the conclusion.
    pub fn imp_right(&mut self, theorem: ThmId, implication: Lit) -> Result<ThmId, KernelError> {
        let (antecedent, consequent) = self.require_binary(implication, Op2::Imp)?;
        let source = self.require_thm(theorem)?;
        let mut premises = source.lhs.to_rows();
        let mut conclusions = source.rhs.to_rows();
        if !remove_unit(&mut premises, antecedent) || !remove_unit(&mut conclusions, consequent) {
            return Err(KernelError::InvalidTheoremRule { rule: "imp right" });
        }
        conclusions.push(unit_row(implication));
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Resolves complementary conclusions of two checked sequents.
    ///
    /// # Errors
    ///
    /// Returns an error unless `pivot` and its complement occur on the
    /// respective right sides.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, pivot: Lit) -> Result<ThmId, KernelError> {
        let lhs = self.require_thm(left)?;
        let rhs = self.require_thm(right)?;
        let mut left_conc = lhs.rhs.to_rows();
        let mut right_conc = rhs.rhs.to_rows();
        if !remove_unit(&mut left_conc, pivot) || !remove_unit(&mut right_conc, pivot.negated()) {
            return Err(KernelError::InvalidTheoremRule { rule: "resolution" });
        }
        let mut premises = lhs.lhs.to_rows();
        premises.extend(rhs.lhs.to_rows());
        let mut conclusions = left_conc;
        conclusions.extend(right_conc);
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Replaces one right-side connective by a sound one-step expansion.
    ///
    /// `branch` selects an operand for conjunctive results and is ignored for
    /// disjunctive results. Repeating this operation expands opcode trees.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the conclusion and names a
    /// supported Boolean opcode with an appropriate branch.
    pub fn expand_conclusion(
        &mut self,
        theorem: ThmId,
        formula: Lit,
        branch: Option<bool>,
    ) -> Result<ThmId, KernelError> {
        let source = self.require_thm(theorem)?;
        let mut conc = source.rhs.to_rows();
        if !remove_unit(&mut conc, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion expansion",
            });
        }
        let replacement = self.expand_right(formula, branch)?;
        conc.extend(replacement.into_iter().map(unit_row));
        self.push_theorem(Thm::new(source.lhs.to_owned(), Dnf::new(conc)))
    }

    /// Recursively flattens a disjunctive opcode tree on the right side.
    ///
    /// Negation is pushed through supported opcodes. The operation rejects a
    /// connective whose flattened form is conjunctive, since choosing a
    /// branch is then required for soundness.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the conclusion and every
    /// compound node has a disjunctive flattened form.
    pub fn flatten_conclusion(
        &mut self,
        theorem: ThmId,
        formula: Lit,
    ) -> Result<ThmId, KernelError> {
        let source = self.require_thm(theorem)?;
        let mut conclusions = source.rhs.to_rows();
        if !remove_unit(&mut conclusions, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion flattening",
            });
        }
        let mut pending = vec![formula];
        let mut leaves = Vec::new();
        while let Some(current) = pending.pop() {
            match self.disjunctive_children(current)? {
                Some(children) => pending.extend(children.into_iter().rev()),
                None => leaves.push(current),
            }
        }
        conclusions.extend(leaves.into_iter().map(unit_row));
        self.push_theorem(Thm::new(source.lhs.to_owned(), Dnf::new(conclusions)))
    }

    /// Recursively flattens a conjunctive opcode tree on the left side.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the premise and every
    /// compound node has a conjunctive flattened form.
    pub fn flatten_premise(&mut self, theorem: ThmId, formula: Lit) -> Result<ThmId, KernelError> {
        let source = self.require_thm(theorem)?;
        let mut premises = source.lhs.to_rows();
        if !remove_unit(&mut premises, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "premise flattening",
            });
        }
        let leaves = self.collect_tree(formula, TreeSide::Conjunctive)?;
        premises.extend(leaves.into_iter().map(unit_row));
        self.push_theorem(Thm::new(Cnf::new(premises), source.rhs.to_owned()))
    }

    /// Folds the leaves of a conjunctive opcode tree on the left side.
    ///
    /// # Errors
    ///
    /// Returns an error unless every flattened leaf occurs in the premise.
    pub fn fold_premise(&mut self, theorem: ThmId, formula: Lit) -> Result<ThmId, KernelError> {
        self.fold_tree(theorem, formula, TreeSide::Conjunctive)
    }

    /// Folds the leaves of a disjunctive opcode tree on the right side.
    ///
    /// # Errors
    ///
    /// Returns an error unless every flattened leaf occurs in the conclusion.
    pub fn fold_conclusion(&mut self, theorem: ThmId, formula: Lit) -> Result<ThmId, KernelError> {
        self.fold_tree(theorem, formula, TreeSide::Disjunctive)
    }

    /// Copies a checked theorem into a newly allocated or reused slot.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent.
    pub fn copy_theorem(&mut self, source: ThmId) -> Result<ThmId, KernelError> {
        self.arena
            .theorems_mut()
            .copy(source)
            .map_err(|_| KernelError::MissingTheorem { id: source })
    }

    /// Removes one theorem. Removed slots are reused by later allocations.
    #[must_use]
    pub fn remove_theorem(&mut self, id: ThmId) -> bool {
        self.arena.theorems_mut().remove(id)
    }

    fn validate_prop(&self, proposition: Lit) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(reference(proposition))
            .map(|_| ())
    }
    fn push_theorem(&mut self, theorem: Thm) -> Result<ThmId, KernelError> {
        self.arena
            .theorems_mut()
            .insert(theorem.0, theorem.1)
            .map_err(|_| KernelError::TooManyTheorems)
    }
    fn push_sequent(
        &mut self,
        premises: &[Lit],
        conclusions: &[Lit],
    ) -> Result<ThmId, KernelError> {
        let theorem = self.checked_sequent(premises, conclusions)?;
        self.push_theorem(theorem)
    }

    fn checked_sequent(&self, premises: &[Lit], conclusions: &[Lit]) -> Result<Thm, KernelError> {
        let premises = self.canonical_props(premises)?;
        let conclusions = self.canonical_props(conclusions)?;
        Ok(Thm::new(
            Cnf::new(premises.into_iter().map(unit_row)),
            Dnf::new(conclusions.into_iter().map(unit_row)),
        ))
    }

    fn replace_theorem(&mut self, id: ThmId, theorem: Thm) -> Result<(), KernelError> {
        self.arena
            .theorems_mut()
            .replace(id, theorem.0, theorem.1)
            .map_err(|_| KernelError::MissingTheorem { id })
    }
    fn signed_bool_value(&self, proposition: Lit) -> Result<Option<bool>, KernelError> {
        self.validate_prop(proposition)?;
        Ok(self.arena.bool_value(reference(proposition)).map(|value| {
            if proposition.is_positive() {
                value
            } else {
                !value
            }
        }))
    }
    fn require_binary(&self, proposition: Lit, expected: Op2) -> Result<(Lit, Lit), KernelError> {
        self.validate_prop(proposition)?;
        if !proposition.is_positive() || self.arena.op2(reference(proposition)) != Some(expected) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "binary connective",
            });
        }
        let mut children =
            self.arena
                .children(reference(proposition))
                .ok_or(KernelError::MissingDefinition {
                    reference: reference(proposition),
                })?;
        let left = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        let right = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        Ok((positive(left), positive(right)))
    }
    fn validate_props(
        &self,
        propositions: impl IntoIterator<Item = Lit>,
    ) -> Result<(), KernelError> {
        for proposition in propositions {
            self.validate_prop(proposition)?;
        }
        Ok(())
    }

    fn decode_cnf(&self, formula: Lit) -> Result<Cnf, KernelError> {
        if !formula.is_positive() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "CNF polarity",
            });
        }
        let mut pending = vec![reference(formula)];
        let mut rows = Vec::new();
        while let Some(current) = pending.pop() {
            if self.arena.bool_value(current) == Some(true) {
                continue;
            }
            if self.arena.op2(current) == Some(Op2::And) {
                let children: Vec<_> = self
                    .arena
                    .children(current)
                    .ok_or(KernelError::MissingDefinition { reference: current })?
                    .collect();
                pending.extend(children.into_iter().rev());
            } else {
                rows.push(self.decode_disjunction(current)?);
            }
        }
        Ok(Cnf::new(rows))
    }

    fn decode_disjunction(&self, formula: Ref) -> Result<LitVec, KernelError> {
        let mut pending = vec![formula];
        let mut row = LitVec::new();
        while let Some(current) = pending.pop() {
            if self.arena.bool_value(current) == Some(false) {
                continue;
            }
            if self.arena.op2(current) == Some(Op2::Or) {
                let children: Vec<_> = self
                    .arena
                    .children(current)
                    .ok_or(KernelError::MissingDefinition { reference: current })?
                    .collect();
                pending.extend(children.into_iter().rev());
            } else {
                row.push(self.decode_canonical_literal(current)?);
            }
        }
        Ok(row)
    }

    fn decode_canonical_literal(&self, term: Ref) -> Result<Lit, KernelError> {
        if self.arena.op1(term) == Some(Op1::Not) {
            let child = self
                .arena
                .children(term)
                .and_then(|mut children| children.next())
                .ok_or(KernelError::InvalidTheoremRule {
                    rule: "canonical negative literal",
                })?;
            self.validate_cnf_atom(child)?;
            return Ok(positive(child).negated());
        }
        self.validate_cnf_atom(term)?;
        Ok(positive(term))
    }

    fn validate_cnf_atom(&self, atom: Ref) -> Result<(), KernelError> {
        self.validate_prop(positive(atom))?;
        if self.arena.op1(atom).is_some()
            || self.arena.op2(atom).is_some()
            || self.arena.bool_value(atom).is_some()
        {
            return Err(KernelError::InvalidTheoremRule {
                rule: "canonical CNF atom",
            });
        }
        Ok(())
    }
    fn canonical_props(&self, propositions: &[Lit]) -> Result<LitVec, KernelError> {
        let mut propositions = propositions.to_vec();
        propositions.sort_unstable();
        propositions.dedup();
        for proposition in &propositions {
            self.validate_prop(*proposition)?;
        }
        Ok(LitVec::from_slice(&propositions))
    }
    fn expand_right(&self, formula: Lit, branch: Option<bool>) -> Result<Vec<Lit>, KernelError> {
        let reference = reference(formula);
        if let Some(value) = self.arena.bool_value(reference) {
            if value != formula.is_positive() {
                return Ok(Vec::new());
            }
            return Err(KernelError::InvalidTheoremRule {
                rule: "true conclusion expansion",
            });
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let signed = |child| {
            let positive = positive(child);
            if formula.is_positive() {
                positive
            } else {
                positive.negated()
            }
        };
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, _) => Ok(vec![signed(children[0]).negated()]),
            (_, Some(Op2::Or), true) | (_, Some(Op2::And), false) => {
                Ok(vec![signed(children[0]), signed(children[1])])
            }
            (_, Some(Op2::And), true) | (_, Some(Op2::Or), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                Ok(vec![signed(children[usize::from(selected)])])
            }
            (_, Some(Op2::Imp), true) => {
                Ok(vec![positive(children[0]).negated(), positive(children[1])])
            }
            (_, Some(Op2::Imp), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                let a = positive(children[0]);
                let b = positive(children[1]).negated();
                Ok(vec![if selected { b } else { a }])
            }
            _ => Err(KernelError::InvalidTheoremRule {
                rule: "conclusion opcode expansion",
            }),
        }
    }

    fn disjunctive_children(&self, formula: Lit) -> Result<Option<Vec<Lit>>, KernelError> {
        let reference = reference(formula);
        if let Some(value) = self.arena.bool_value(reference) {
            if value != formula.is_positive() {
                return Ok(Some(Vec::new()));
            }
            return Ok(None);
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let positive = positive;
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, true) => Ok(Some(vec![positive(children[0]).negated()])),
            (Some(Op1::Not), _, false) => Ok(Some(vec![positive(children[0])])),
            (_, Some(Op2::Or), true) => {
                Ok(Some(vec![positive(children[0]), positive(children[1])]))
            }
            (_, Some(Op2::And), false) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Imp), true) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]),
            ])),
            (_, Some(Op2::And), true) | (_, Some(Op2::Or | Op2::Imp), false) => {
                Err(KernelError::InvalidTheoremRule {
                    rule: "disjunctive conclusion flattening",
                })
            }
            _ => Ok(None),
        }
    }

    fn conjunctive_children(&self, formula: Lit) -> Result<Option<Vec<Lit>>, KernelError> {
        let reference = reference(formula);
        if let Some(value) = self.arena.bool_value(reference) {
            if value == formula.is_positive() {
                return Ok(Some(Vec::new()));
            }
            return Ok(None);
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let positive = positive;
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, true) => Ok(Some(vec![positive(children[0]).negated()])),
            (Some(Op1::Not), _, false) => Ok(Some(vec![positive(children[0])])),
            (_, Some(Op2::And), true) => {
                Ok(Some(vec![positive(children[0]), positive(children[1])]))
            }
            (_, Some(Op2::Or), false) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Imp), false) => Ok(Some(vec![
                positive(children[0]),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Or | Op2::Imp), true) | (_, Some(Op2::And), false) => {
                Err(KernelError::InvalidTheoremRule {
                    rule: "conjunctive premise flattening",
                })
            }
            _ => Ok(None),
        }
    }

    fn collect_tree(&self, formula: Lit, side: TreeSide) -> Result<LitVec, KernelError> {
        let mut pending = vec![formula];
        let mut leaves = LitVec::new();
        while let Some(current) = pending.pop() {
            let children = match side {
                TreeSide::Conjunctive => self.conjunctive_children(current)?,
                TreeSide::Disjunctive => self.disjunctive_children(current)?,
            };
            match children {
                Some(children) => pending.extend(children.into_iter().rev()),
                None => leaves.push(current),
            }
        }
        Ok(leaves)
    }

    fn fold_tree(
        &mut self,
        theorem: ThmId,
        formula: Lit,
        side: TreeSide,
    ) -> Result<ThmId, KernelError> {
        let source = self.require_thm(theorem)?;
        let leaves = self.collect_tree(formula, side)?;
        let mut premises = source.lhs.to_rows();
        let mut conclusions = source.rhs.to_rows();
        let matched = match side {
            TreeSide::Conjunctive => leaves.iter().all(|leaf| remove_unit(&mut premises, *leaf)),
            TreeSide::Disjunctive => leaves
                .iter()
                .all(|leaf| remove_unit(&mut conclusions, *leaf)),
        };
        if !matched {
            return Err(KernelError::InvalidTheoremRule {
                rule: "opcode tree folding",
            });
        }
        match side {
            TreeSide::Conjunctive => premises.push(unit_row(formula)),
            TreeSide::Disjunctive => conclusions.push(unit_row(formula)),
        }
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }
}

#[derive(Clone, Copy)]
enum TreeSide {
    Conjunctive,
    Disjunctive,
}

fn sole_positive_conclusion(theorem: ThmRef<'_>) -> Result<Ref, KernelError> {
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(KernelError::InvalidTheoremRule {
        rule: "AP_THM single conclusion",
    })?;
    if rows.next().is_some() || row.len() != 1 {
        return Err(KernelError::InvalidTheoremRule {
            rule: "AP_THM single conclusion",
        });
    }
    let literal = row[0];
    if !literal.is_positive() {
        return Err(KernelError::InvalidTheoremRule {
            rule: "AP_THM positive equality",
        });
    }
    Ok(reference(literal))
}

fn replace_atom(row: &[Lit], source: Ref, target: Ref) -> LitVec {
    row.iter()
        .copied()
        .map(|literal| {
            if reference(literal) != source {
                return literal;
            }
            let replacement = positive(target);
            if literal.is_positive() {
                replacement
            } else {
                replacement.negated()
            }
        })
        .collect()
}

fn unit_row(proposition: Lit) -> LitVec {
    std::iter::once(proposition).collect()
}

fn remove_unit(rows: &mut Vec<LitVec>, proposition: Lit) -> bool {
    remove_unit_row(rows, proposition, LitVec::as_slice)
}

fn remove_unit_row<T>(rows: &mut Vec<T>, proposition: Lit, literals: fn(&T) -> &[Lit]) -> bool {
    let Some(index) = rows.iter().position(|row| literals(row) == [proposition]) else {
        return false;
    };
    rows.remove(index);
    true
}

fn remove_unit_pair(rows: &mut Vec<LitVec>, left: Lit, right: Lit) -> bool {
    if !remove_unit(rows, left) {
        return false;
    }
    left == right || remove_unit(rows, right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    struct Fixture {
        kernel: Kernel,
        p: Lit,
        q: Lit,
    }

    fn fixture() -> Fixture {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let p = kernel.tm_fv(1, bool_ty).unwrap();
        let q = kernel.tm_fv(2, bool_ty).unwrap();
        Fixture {
            kernel,
            p: positive(p),
            q: positive(q),
        }
    }

    fn cnf_id(position: usize) -> CnfId {
        let one_based = position.checked_add(1).unwrap();
        CnfId::new(i32::try_from(one_based).unwrap()).unwrap()
    }

    fn dnf_id(position: usize) -> DnfId {
        let one_based = position.checked_add(1).unwrap();
        DnfId::new(i32::try_from(one_based).unwrap()).unwrap()
    }

    fn unit_premises(theorem: ThmRef<'_>) -> Vec<Lit> {
        theorem
            .lhs
            .rows()
            .map(|row| *row.first().filter(|_| row.len() == 1).unwrap())
            .collect()
    }

    fn unit_conclusions(theorem: ThmRef<'_>) -> Vec<Lit> {
        theorem
            .rhs
            .rows()
            .map(|row| *row.first().filter(|_| row.len() == 1).unwrap())
            .collect()
    }

    fn snapshot(theorem: ThmRef<'_>) -> (Vec<LitVec>, Vec<LitVec>) {
        (theorem.lhs.to_rows(), theorem.rhs.to_rows())
    }

    #[test]
    fn signed_ids_use_inverted_polarity_without_overflow() {
        let term = Ref::new(7).unwrap();
        let positive = positive(term);
        assert_eq!(positive.get(), -7);
        assert!(positive.is_positive());
        assert_eq!(reference(positive), term);
        assert_eq!(positive.negated().get(), 7);
        assert_eq!(Lit::try_new(0), Err(LitError { value: 0 }));
        assert_eq!(Lit::try_new(i32::MIN), Err(LitError { value: i32::MIN }));
        assert_eq!(Lit::try_new(i32::MAX), Err(LitError { value: i32::MAX }));
        assert_eq!(Lit::try_new(-i32::MAX), Err(LitError { value: -i32::MAX }));
    }

    #[test]
    fn theorem_conversion_replaces_both_polarities_transactionally() {
        let Fixture { mut kernel, p, q } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let binder = kernel.tm_fv(3, bool_ty).unwrap();
        let identity_function = kernel.lam(binder, binder).unwrap();
        let application = kernel.app(identity_function, reference(p)).unwrap();
        let substitution = kernel.syn_sub_var(None, binder, reference(p)).unwrap();
        let beta = kernel
            .tm_beta_fact(None, application, substitution)
            .unwrap();
        kernel.union_syn_fact(beta).unwrap();

        let source = positive(application);
        let positive_theorem = kernel.identity(source).unwrap();
        kernel
            .convert_theorem(positive_theorem, application, reference(p))
            .unwrap();
        let converted = kernel.thm().get(positive_theorem).unwrap();
        assert_eq!(unit_premises(converted), [p]);
        assert_eq!(unit_conclusions(converted), [p]);

        let negative_theorem = kernel.identity(source.negated()).unwrap();
        kernel
            .convert_theorem(negative_theorem, application, reference(p))
            .unwrap();
        let converted = kernel.thm().get(negative_theorem).unwrap();
        assert_eq!(unit_premises(converted), [p.negated()]);
        assert_eq!(unit_conclusions(converted), [p.negated()]);

        let before = snapshot(kernel.thm().get(positive_theorem).unwrap());
        assert!(
            kernel
                .convert_theorem(positive_theorem, reference(p), reference(q))
                .is_err()
        );
        assert_eq!(
            snapshot(kernel.thm().get(positive_theorem).unwrap()),
            before
        );
    }

    #[test]
    fn conclusion_conversion_leaves_a_shared_premise_atom_alone() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let binder = kernel.tm_fv(9, bool_ty).unwrap();
        let identity_function = kernel.lam(binder, binder).unwrap();
        let application = kernel.app(identity_function, reference(p)).unwrap();
        let substitution = kernel.syn_sub_var(None, binder, reference(p)).unwrap();
        let beta = kernel
            .tm_beta_fact(None, application, substitution)
            .unwrap();
        kernel.union_syn_fact(beta).unwrap();

        let theorem = kernel.identity(positive(application)).unwrap();
        kernel
            .convert_conclusions(theorem, application, reference(p))
            .unwrap();
        let converted = kernel.thm().get(theorem).unwrap();
        assert_eq!(unit_premises(converted), [positive(application)]);
        assert_eq!(unit_conclusions(converted), [p]);
    }

    #[test]
    fn ap_thm_builds_an_exact_applied_equality_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let function_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = kernel.tm_fv(10, function_ty).unwrap();
        let varied = kernel.tm_fv(11, function_ty).unwrap();
        let source = kernel.eq(bool_ty, function, varied).unwrap();
        // The generic theorem inserter is private to this module. It stands in
        // for any earlier checked HOL rule producing the exact equality.
        let premise = kernel.push_sequent(&[], &[positive(source)]).unwrap();

        let applied = kernel.ap_thm(premise, reference(p)).unwrap();
        assert_eq!(
            kernel.arena().tag(applied.left),
            Some(crate::Tag::Tm(crate::TmTag::App))
        );
        assert_eq!(
            kernel.arena().tag(applied.right),
            Some(crate::Tag::Tm(crate::TmTag::App))
        );
        assert_eq!(
            kernel.arena().tag(applied.equality),
            Some(crate::Tag::Tm(crate::TmTag::Eq))
        );
        assert_eq!(
            unit_conclusions(kernel.require_thm(applied.theorem).unwrap()),
            [positive(applied.equality)]
        );
        assert!(
            kernel
                .require_thm(applied.theorem)
                .unwrap()
                .lhs
                .rows()
                .next()
                .is_none()
        );

        let contextual = kernel.identity(positive(source)).unwrap();
        let contextual_result = kernel.ap_thm(contextual, reference(p)).unwrap();
        assert_eq!(
            unit_premises(kernel.require_thm(contextual_result.theorem).unwrap()),
            [positive(source)]
        );

        let nonexact = kernel.push_sequent(&[], &[positive(source), p]).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.ap_thm(nonexact, reference(p)).is_err());
        assert_eq!(*kernel.arena(), before);

        let before = kernel.arena().clone();
        assert!(kernel.ap_thm(premise, bool_ty).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn reflexivity_builds_an_exact_theorem_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let result = kernel.refl(bool_ty, reference(p)).unwrap();
        assert_eq!(
            kernel
                .arena()
                .children(result.equality)
                .unwrap()
                .collect::<Vec<_>>(),
            [bool_ty, reference(p), reference(p)]
        );
        let theorem = kernel.require_thm(result.theorem).unwrap();
        assert!(theorem.lhs.rows().next().is_none());
        assert_eq!(unit_conclusions(theorem), [positive(result.equality)]);

        let before = kernel.arena().clone();
        assert!(kernel.refl(reference(p), reference(p)).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn deduction_antisymmetry_discharges_unit_premises_transactionally() {
        let Fixture {
            mut kernel, p, q, ..
        } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p).unwrap();
        let result = kernel
            .deduct_antisym(bool_ty, reference(p), reference(p), left, right)
            .unwrap();
        assert_eq!(
            kernel
                .arena()
                .children(result.equality)
                .unwrap()
                .collect::<Vec<_>>(),
            [bool_ty, reference(p), reference(p)]
        );
        let theorem = kernel.require_thm(result.theorem).unwrap();
        assert!(theorem.lhs.rows().next().is_none());
        assert_eq!(unit_conclusions(theorem), [positive(result.equality)]);

        let nonexact = kernel.push_sequent(&[], &[p, q]).unwrap();
        let before = kernel.arena().clone();
        assert!(
            kernel
                .deduct_antisym(bool_ty, reference(p), reference(p), nonexact, right)
                .is_err()
        );
        assert_eq!(*kernel.arena(), before);

        let before = kernel.arena().clone();
        assert!(
            kernel
                .deduct_antisym(reference(p), reference(p), reference(p), left, right)
                .is_err()
        );
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn abstraction_congruence_checks_freshness_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let binder = kernel.tm_fv(700, bool_ty).unwrap();
        let source = kernel.refl(bool_ty, reference(p)).unwrap();

        let abstracted = kernel.abs_thm(source.theorem, binder).unwrap();
        let function_ty = kernel.classifier(abstracted.left).unwrap();
        assert_eq!(kernel.classifier(abstracted.right).unwrap(), function_ty);
        kernel
            .type_arrow_member::<std::convert::Infallible>(function_ty)
            .unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(abstracted.theorem).unwrap()),
            [positive(abstracted.equality)]
        );
        assert!(
            kernel
                .require_thm(abstracted.theorem)
                .unwrap()
                .lhs
                .rows()
                .next()
                .is_none()
        );

        let truth = kernel.bool(bool_ty, true).unwrap();
        let contextual = kernel.copy_theorem(source.theorem).unwrap();
        kernel.weaken(contextual, &[positive(truth)], &[]).unwrap();
        let contextual = kernel.abs_thm(contextual, binder).unwrap();
        assert_eq!(
            unit_premises(kernel.require_thm(contextual.theorem).unwrap()),
            [positive(truth)]
        );

        let captures = kernel.eq(bool_ty, binder, binder).unwrap();
        let captures_theorem = kernel.copy_theorem(source.theorem).unwrap();
        kernel
            .weaken(captures_theorem, &[positive(captures)], &[])
            .unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.abs_thm(captures_theorem, binder).is_err());
        assert_eq!(*kernel.arena(), before);

        let before = kernel.arena().clone();
        assert!(kernel.abs_thm(source.theorem, bool_ty).is_err());
        assert_eq!(*kernel.arena(), before);

        let malformed = kernel.push_sequent(&[], &[p]).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.abs_thm(malformed, binder).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn eqt_elim_requires_an_exact_right_truth_equality() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let equality = kernel.eq(bool_ty, reference(p), truth).unwrap();
        let source = kernel.push_sequent(&[], &[positive(equality)]).unwrap();
        let theorem = kernel.eqt_elim(source).unwrap();
        assert_eq!(unit_premises(kernel.require_thm(theorem).unwrap()), []);
        assert_eq!(unit_conclusions(kernel.require_thm(theorem).unwrap()), [p]);

        let reversed = kernel.eq(bool_ty, truth, reference(p)).unwrap();
        let reversed = kernel.push_sequent(&[], &[positive(reversed)]).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.eqt_elim(reversed).is_err());
        assert_eq!(*kernel.arena(), before);

        let contextual = kernel.identity(positive(equality)).unwrap();
        let contextual_result = kernel.eqt_elim(contextual).unwrap();
        assert_eq!(
            unit_premises(kernel.require_thm(contextual_result).unwrap()),
            [positive(equality)]
        );

        let nonexact = kernel.push_sequent(&[], &[positive(equality), p]).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.eqt_elim(nonexact).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn forall_intro_generalizes_only_an_exact_assertion_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let binder = kernel.tm_fv(12, bool_ty).unwrap();
        let exact = kernel.push_sequent(&[], &[p]).unwrap();

        let generalized = kernel.forall_intro(exact, binder).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(generalized.theorem).unwrap()),
            [positive(generalized.universal)]
        );
        assert!(
            kernel
                .require_thm(generalized.theorem)
                .unwrap()
                .lhs
                .rows()
                .next()
                .is_none()
        );
        assert_eq!(
            kernel.arena().tag(generalized.universal),
            Some(crate::Tag::Tm(crate::TmTag::Eq))
        );

        let contextual = kernel.identity(p).unwrap();
        let contextual_result = kernel.forall_intro(contextual, binder).unwrap();
        assert_eq!(
            unit_premises(kernel.require_thm(contextual_result.theorem).unwrap()),
            [p]
        );

        let captures = kernel.identity(positive(binder)).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.forall_intro(captures, binder).is_err());
        assert_eq!(*kernel.arena(), before);

        let before = kernel.arena().clone();
        assert!(kernel.forall_intro(exact, bool_ty).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn type_forall_intro_accepts_only_one_premise_free_assertion() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let name = 44;
        let parameter = kernel.ty_fv(name, star).unwrap();
        let value = kernel.tm_fv(45, parameter).unwrap();
        let proved = kernel.refl(bool_ty, value).unwrap();

        let generalized = kernel.ty_forall_intro(proved.theorem, name).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(generalized.theorem).unwrap()),
            [positive(generalized.universal)]
        );
        assert!(
            kernel
                .require_thm(generalized.theorem)
                .unwrap()
                .lhs
                .rows()
                .next()
                .is_none()
        );
        assert!(matches!(
            kernel
                .row::<std::convert::Infallible>(generalized.universal)
                .unwrap()
                .expr(),
            Node::TyForall {
                name: 44,
                predicate
            } if *predicate == proved.equality
        ));

        let contextual = kernel.identity(positive(proved.equality)).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.ty_forall_intro(contextual, name).is_err());
        assert_eq!(*kernel.arena(), before);

        let nonexact = kernel.copy_theorem(proved.theorem).unwrap();
        kernel
            .weaken(nonexact, &[], &[positive(generalized.universal)])
            .unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.ty_forall_intro(nonexact, name).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn choice_intro_preserves_context_and_selects_from_the_same_predicate() {
        let Fixture { mut kernel, p, .. } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let predicate_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let predicate = kernel.tm_fv(13, predicate_ty).unwrap();
        let application = kernel.app(predicate, reference(p)).unwrap();
        let source = kernel.identity(positive(application)).unwrap();

        let chosen = kernel.choice_intro(source).unwrap();
        assert_eq!(
            kernel.arena().tag(chosen.witness),
            Some(crate::Tag::Tm(crate::TmTag::Eps))
        );
        assert_eq!(
            kernel
                .arena()
                .children(chosen.proposition)
                .unwrap()
                .collect::<Vec<_>>(),
            [predicate, chosen.witness]
        );
        let result = kernel.require_thm(chosen.theorem).unwrap();
        assert_eq!(unit_premises(result), [positive(application)]);
        assert_eq!(unit_conclusions(result), [positive(chosen.proposition)]);

        let malformed = kernel.identity(p).unwrap();
        let before = kernel.arena().clone();
        assert!(kernel.choice_intro(malformed).is_err());
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn ap_term_and_eq_mp_preserve_and_combine_contexts() {
        let Fixture { mut kernel, p, q } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let equality = kernel.eq(bool_ty, reference(p), reference(q)).unwrap();
        let equality_theorem = kernel.identity(positive(equality)).unwrap();
        let function_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = kernel.tm_fv(14, function_ty).unwrap();

        let applied = kernel.ap_term(equality_theorem, function).unwrap();
        let applied_theorem = kernel.require_thm(applied.theorem).unwrap();
        assert_eq!(unit_premises(applied_theorem), [positive(equality)]);
        assert_eq!(
            unit_conclusions(applied_theorem),
            [positive(applied.equality)]
        );

        let proposition_equality = kernel.eq(bool_ty, reference(p), reference(q)).unwrap();
        let proposition_equality_theorem = kernel
            .push_sequent(&[], &[positive(proposition_equality)])
            .unwrap();
        let premise_theorem = kernel.identity(p).unwrap();
        let rewritten = kernel
            .eq_mp(proposition_equality_theorem, premise_theorem)
            .unwrap();
        let rewritten = kernel.require_thm(rewritten).unwrap();
        assert_eq!(unit_premises(rewritten), [p]);
        assert_eq!(unit_conclusions(rewritten), [q]);

        let wrong_premise = kernel.identity(q).unwrap();
        let before = kernel.arena().clone();
        assert!(
            kernel
                .eq_mp(proposition_equality_theorem, wrong_premise)
                .is_err()
        );
        assert_eq!(*kernel.arena(), before);
    }

    #[test]
    fn theorem_contexts_preserve_order_and_duplicates_after_in_place_weakening() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        kernel.weaken(identity, &[q, p, q], &[q, p, q]).unwrap();
        let expected = [p, q, p, q];
        assert_eq!(
            unit_premises(kernel.require_thm(identity).unwrap()),
            expected
        );
        assert_eq!(
            unit_conclusions(kernel.require_thm(identity).unwrap()),
            expected
        );
        assert!(
            !kernel
                .require_thm(identity)
                .unwrap()
                .lhs
                .rows()
                .next()
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn weakening_preserves_hostile_unsorted_input_transactionally() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        kernel
            .weaken(identity, &[q, p.negated(), q, p], &[q.negated(), p, q])
            .unwrap();
        let expected_premises = vec![p, q, p.negated(), q, p];
        let expected_conclusions = vec![p, q.negated(), p, q];
        assert_eq!(
            unit_premises(kernel.require_thm(identity).unwrap()),
            expected_premises
        );
        assert_eq!(
            unit_conclusions(kernel.require_thm(identity).unwrap()),
            expected_conclusions
        );
    }

    #[test]
    fn matrix_weakening_and_indexed_transfer_preserve_non_unit_rows() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let mut cnf_row: LitVec = [q, p.negated()].into_iter().collect();
        cnf_row.sort_unstable();
        cnf_row.dedup();
        let mut dnf_row: LitVec = [q.negated(), p].into_iter().collect();
        dnf_row.sort_unstable();
        dnf_row.dedup();
        kernel
            .weaken_matrix(
                theorem,
                std::slice::from_ref(&cnf_row),
                std::slice::from_ref(&dnf_row),
            )
            .unwrap();

        let cnf_index = kernel
            .require_thm(theorem)
            .unwrap()
            .lhs
            .rows()
            .position(|candidate| candidate == cnf_row.as_slice())
            .unwrap();
        kernel.move_cnf_right(theorem, cnf_id(cnf_index)).unwrap();
        assert!(
            kernel
                .require_thm(theorem)
                .unwrap()
                .rhs
                .rows()
                .any(|candidate| candidate == [q.negated(), p])
        );

        let dnf_index = kernel
            .require_thm(theorem)
            .unwrap()
            .rhs
            .rows()
            .position(|candidate| candidate == dnf_row.as_slice())
            .unwrap();
        kernel.move_dnf_left(theorem, dnf_id(dnf_index)).unwrap();
        assert!(
            kernel
                .require_thm(theorem)
                .unwrap()
                .lhs
                .rows()
                .any(|candidate| candidate == [p.negated(), q])
        );
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn matrix_mutations_reject_bad_inputs_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let before = snapshot(kernel.require_thm(theorem).unwrap());
        let missing = Lit::new(-999_999);
        assert!(
            kernel
                .weaken_matrix(theorem, &[std::iter::once(missing).collect()], &[])
                .is_err()
        );
        assert_eq!(snapshot(kernel.require_thm(theorem).unwrap()), before);
        assert!(
            kernel
                .move_cnf_right(theorem, CnfId::new(i32::MAX).unwrap())
                .is_err()
        );
        assert!(
            kernel
                .move_dnf_left(theorem, DnfId::new(i32::MAX).unwrap())
                .is_err()
        );
        assert_eq!(snapshot(kernel.require_thm(theorem).unwrap()), before);
    }

    #[test]
    fn deletion_reuses_only_ephemeral_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let p_id = kernel.identity(p).unwrap();
        let q_id = kernel.identity(q).unwrap();
        assert!(kernel.remove_theorem(p_id));
        assert!(!kernel.remove_theorem(p_id));
        assert!(kernel.require_thm(q_id).is_ok());
        assert!(matches!(
            kernel.require_thm(p_id),
            Err(KernelError::MissingTheorem { .. })
        ));
        assert_eq!(kernel.identity(q.negated()).unwrap(), p_id);
        assert!(kernel.require_thm(q_id).is_ok());
    }

    #[test]
    fn deletion_with_an_absent_handle_is_false_and_reuse_is_lifo() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.identity(p).unwrap();
        let second = kernel.identity(q).unwrap();
        let absent = ThmId::new(second.get() + 1).unwrap();
        assert!(!kernel.remove_theorem(absent));
        assert!(kernel.require_thm(first).is_ok());
        assert!(kernel.require_thm(second).is_ok());

        assert!(kernel.remove_theorem(first));
        assert!(kernel.remove_theorem(second));
        assert!(kernel.require_thm(first).is_err());
        assert!(kernel.require_thm(second).is_err());
        assert_eq!(kernel.identity(p.negated()).unwrap(), second);
        assert_eq!(kernel.identity(q.negated()).unwrap(), first);
    }

    #[test]
    fn checked_theorems_are_owned_and_serialized_by_the_arena() {
        let Fixture { mut kernel, p, .. } = fixture();
        let before = kernel.arena().clone();
        let theorem = kernel.identity(p).unwrap();
        assert!(kernel.require_thm(theorem).is_ok());
        assert_ne!(kernel.arena(), &before);

        let arena = kernel.into_arena();
        assert_eq!(arena.theorems().get(theorem).unwrap().lhs.rows().count(), 1);
        let mut encoded = Vec::new();
        crate::wire::serialize(&arena, &mut encoded).unwrap();
        let decoded = crate::wire::deserialize(encoded.as_slice()).unwrap();
        assert_eq!(
            decoded.theorems().get(theorem),
            arena.theorems().get(theorem)
        );
    }

    #[test]
    fn conclusion_constant_expansion_eliminates_exactly_signed_false() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let falsehood = positive(kernel.bool(bool_ty, false).unwrap());
        let truth = positive(kernel.bool(bool_ty, true).unwrap());

        for signed_false in [falsehood, truth.negated()] {
            let identity = kernel.identity(signed_false).unwrap();
            let expanded = kernel
                .expand_conclusion(identity, signed_false, None)
                .unwrap();
            assert!(
                kernel
                    .require_thm(expanded)
                    .unwrap()
                    .rhs
                    .rows()
                    .next()
                    .is_none()
            );
        }

        for signed_true in [truth, falsehood.negated()] {
            let identity = kernel.identity(signed_true).unwrap();
            assert!(
                kernel
                    .expand_conclusion(identity, signed_true, None)
                    .is_err()
            );
        }
    }

    #[test]
    fn weakening_resolution_and_polarity_transfer_form_sound_sequents() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        kernel.weaken(assumed_p, &[], &[q]).unwrap();
        kernel.weaken(assumed_not_p, &[], &[q]).unwrap();
        let (left, right) = (assumed_p, assumed_not_p);
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(resolved).unwrap()),
            [q, q]
        );

        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        let contradiction = kernel.resolve(assumed_p, assumed_not_p, p).unwrap();
        kernel.weaken(contradiction, &[q], &[]).unwrap();
        kernel.not_right(contradiction, q).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(contradiction).unwrap()),
            [q.negated()]
        );
    }

    #[test]
    fn opcode_tree_expansion_refutes_p_and_not_p() {
        let Fixture { mut kernel, p, .. } = fixture();
        let not_p_ref = kernel.op1(Op1::Not, reference(p)).unwrap();
        let not_p = positive(not_p_ref);
        let formula_ref = kernel.op2(Op2::And, reference(p), not_p_ref).unwrap();
        let formula = positive(formula_ref);
        let root = kernel.identity(formula).unwrap();
        let p_clause = kernel
            .expand_conclusion(root, formula, Some(false))
            .unwrap();
        let not_clause = kernel.expand_conclusion(root, formula, Some(true)).unwrap();
        let neg_p_clause = kernel.expand_conclusion(not_clause, not_p, None).unwrap();
        let refutation = kernel.resolve(p_clause, neg_p_clause, p).unwrap();
        let sequent = kernel.require_thm(refutation).unwrap();
        assert_eq!(unit_premises(sequent), [formula, formula]);
        assert!(sequent.rhs.rows().next().is_none());
    }

    #[test]
    fn recursive_flattening_handles_or_not_imp_and_false() {
        let Fixture { mut kernel, p, q } = fixture();
        let not_p = kernel.op1(Op1::Not, reference(p)).unwrap();
        let implication = kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap();
        let nested = kernel.op2(Op2::Or, not_p, implication).unwrap();
        let nested = positive(nested);
        let theorem = kernel.identity(nested).unwrap();
        let flattened = kernel.flatten_conclusion(theorem, nested).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(flattened).unwrap()),
            [p.negated(), p.negated(), q]
        );

        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let falsehood = positive(falsehood);
        let false_theorem = kernel.identity(falsehood).unwrap();
        let eliminated = kernel
            .expand_conclusion(false_theorem, falsehood, None)
            .unwrap();
        assert!(
            kernel
                .require_thm(eliminated)
                .unwrap()
                .rhs
                .rows()
                .next()
                .is_none()
        );
    }

    #[test]
    fn recursive_tree_folding_round_trips_both_sides() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let conjunction_id = kernel.identity(conjunction).unwrap();
        let flat_left = kernel.flatten_premise(conjunction_id, conjunction).unwrap();
        let folded_left = kernel.fold_premise(flat_left, conjunction).unwrap();
        assert_eq!(
            kernel.require_thm(folded_left).unwrap(),
            kernel.require_thm(conjunction_id).unwrap()
        );

        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
        let disjunction_id = kernel.identity(disjunction).unwrap();
        let flat_right = kernel
            .flatten_conclusion(disjunction_id, disjunction)
            .unwrap();
        let folded_right = kernel.fold_conclusion(flat_right, disjunction).unwrap();
        assert_eq!(
            kernel.require_thm(folded_right).unwrap(),
            kernel.require_thm(disjunction_id).unwrap()
        );
    }

    #[test]
    fn recursive_tree_folding_preserves_repeated_leaves() {
        let Fixture { mut kernel, p, .. } = fixture();
        let repeated_and = positive(kernel.op2(Op2::And, reference(p), reference(p)).unwrap());
        let nested_and = positive(
            kernel
                .op2(Op2::And, reference(repeated_and), reference(p))
                .unwrap(),
        );
        let and_identity = kernel.identity(nested_and).unwrap();
        let flat_left = kernel.flatten_premise(and_identity, nested_and).unwrap();
        assert_eq!(
            unit_premises(kernel.require_thm(flat_left).unwrap()),
            [p, p, p]
        );
        let folded_left = kernel.fold_premise(flat_left, nested_and).unwrap();
        assert_eq!(
            kernel.require_thm(folded_left).unwrap(),
            kernel.require_thm(and_identity).unwrap()
        );

        let repeated_or = positive(kernel.op2(Op2::Or, reference(p), reference(p)).unwrap());
        let nested_or = positive(
            kernel
                .op2(Op2::Or, reference(repeated_or), reference(p))
                .unwrap(),
        );
        let or_identity = kernel.identity(nested_or).unwrap();
        let flat_right = kernel.flatten_conclusion(or_identity, nested_or).unwrap();
        assert_eq!(
            unit_conclusions(kernel.require_thm(flat_right).unwrap()),
            [p, p, p]
        );
        let folded_right = kernel.fold_conclusion(flat_right, nested_or).unwrap();
        assert_eq!(
            kernel.require_thm(folded_right).unwrap(),
            kernel.require_thm(or_identity).unwrap()
        );
    }

    #[test]
    fn primitive_resolution_is_valid_for_every_boolean_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        kernel.weaken(assumed_p, &[q], &[q]).unwrap();
        kernel.weaken(assumed_not_p, &[q], &[q.negated()]).unwrap();
        let (left, right) = (assumed_p, assumed_not_p);
        let result = kernel.resolve(left, right, p).unwrap();
        for p_value in [false, true] {
            for q_value in [false, true] {
                assert!(valid(
                    kernel.require_thm(left).unwrap(),
                    p,
                    p_value,
                    q,
                    q_value
                ));
                assert!(valid(
                    kernel.require_thm(right).unwrap(),
                    p,
                    p_value,
                    q,
                    q_value
                ));
                assert!(valid(
                    kernel.require_thm(result).unwrap(),
                    p,
                    p_value,
                    q,
                    q_value
                ));
            }
        }
    }

    #[test]
    fn identity_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.identity(p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn weakening_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        kernel.weaken(assumed, &[q], &[q.negated()]).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
    }

    #[test]
    fn cut_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p).unwrap();
        let theorem = kernel.cut(left, right, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn constants_are_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let falsehood = positive(kernel.bool(bool_ty, false).unwrap());
        let truth = positive(kernel.bool(bool_ty, true).unwrap());
        let false_left = kernel.false_left(falsehood).unwrap();
        let true_right = kernel.true_right(truth).unwrap();
        assert_valid(&kernel, false_left, &[p, q]);
        assert_valid(&kernel, true_right, &[p, q]);
    }

    #[test]
    fn not_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        kernel.not_left(assumed, p).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
    }

    #[test]
    fn not_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        kernel.not_right(assumed, p).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
    }

    #[test]
    fn and_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(p).unwrap();
        kernel.weaken(assumed, &[q], &[]).unwrap();
        let theorem = kernel.and_left(assumed, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.and_right(left, right, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.or_left(left, right, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(p).unwrap();
        kernel.weaken(assumed, &[], &[q]).unwrap();
        let theorem = kernel.or_right(assumed, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication = positive(kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.imp_left(left, right, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication = positive(kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(q).unwrap();
        kernel.weaken(assumed, &[p], &[]).unwrap();
        let theorem = kernel.imp_right(assumed, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn rejected_rules_do_not_allocate_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.identity(p).unwrap();
        assert!(kernel.cut(first, first, q).is_err());
        let second = kernel.identity(q).unwrap();
        assert_eq!(second.get(), first.get() + 1);
        assert!(kernel.and_left(first, q).is_err());
        let third = kernel.identity(q.negated()).unwrap();
        assert_eq!(third.get(), second.get() + 1);
    }

    #[test]
    fn only_explicit_in_place_rules_mutate_their_evidence_transactionally() {
        let Fixture { mut kernel, p, q } = fixture();
        let unary = kernel.identity(p).unwrap();
        let preserved = kernel.copy_theorem(unary).unwrap();
        kernel.weaken(unary, &[q], &[]).unwrap();
        let expected = [p, q];
        assert_eq!(unit_premises(kernel.require_thm(unary).unwrap()), expected);
        assert_eq!(unit_premises(kernel.require_thm(preserved).unwrap()), [p]);
        let before = snapshot(kernel.require_thm(unary).unwrap());
        let missing = Lit::new(-999_999);
        assert!(kernel.weaken(unary, &[missing], &[]).is_err());
        assert_eq!(snapshot(kernel.require_thm(unary).unwrap()), before);
        assert!(kernel.and_left(unary, q).is_err());
        assert_eq!(snapshot(kernel.require_thm(unary).unwrap()), before);

        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p.negated()).unwrap();
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_ne!(resolved, left);
        assert_ne!(resolved, right);
        assert_eq!(
            unit_premises(kernel.require_thm(resolved).unwrap()),
            [p, p.negated()]
        );
        assert!(
            kernel
                .require_thm(resolved)
                .unwrap()
                .rhs
                .rows()
                .next()
                .is_none()
        );
        assert_eq!(unit_conclusions(kernel.require_thm(left).unwrap()), [p]);
        assert_eq!(
            unit_conclusions(kernel.require_thm(right).unwrap()),
            [p.negated()]
        );
    }

    #[test]
    fn every_in_place_rule_preserves_the_exact_theorem_on_rejection() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let original = snapshot(kernel.require_thm(theorem).unwrap());
        let missing = Lit::new(-999_999);

        assert!(kernel.weaken(theorem, &[missing], &[]).is_err());
        assert_eq!(snapshot(kernel.require_thm(theorem).unwrap()), original);

        assert!(kernel.not_left(theorem, q).is_err());
        assert_eq!(snapshot(kernel.require_thm(theorem).unwrap()), original);

        assert!(kernel.not_right(theorem, q).is_err());
        assert_eq!(snapshot(kernel.require_thm(theorem).unwrap()), original);
    }

    #[test]
    fn universal_syllogisms_allow_atoms_without_resident_boolean_rows() {
        let atom = Lit::new(i32::MAX - 1);
        let mut source = SyllogismKernel::new();
        let universal = source.identity(atom).unwrap();
        let mut kernel = Kernel::new();

        let syllogism = kernel.syl_mut().copy_from(&source, universal).unwrap();
        let theorem = kernel.thm_mut().copy_from(&source, universal).unwrap();

        assert_eq!(
            kernel.syl().get(syllogism).unwrap(),
            source.get(universal).unwrap()
        );
        assert_eq!(
            kernel.require_thm(theorem).unwrap(),
            source.get(universal).unwrap()
        );
        assert!(kernel.identity(atom).is_err());
    }

    #[test]
    fn completed_refutations_copy_into_syl_and_thm_through_checked_views() {
        let atom = Lit::new(i32::MAX - 1);
        let refutation = Refuter::new(Cnf::new([LitVec::new(), std::iter::once(atom).collect()]))
            .done()
            .unwrap();
        let mut kernel = Kernel::new();

        let syllogism = kernel.syl_mut().copy_refutation(&refutation).unwrap();
        let theorem = kernel.thm_mut().copy_refutation(&refutation).unwrap();

        assert_eq!(kernel.syl().get(syllogism), Some(refutation.theorem()));
        assert_eq!(kernel.require_thm(theorem).unwrap(), refutation.theorem());
        assert!(kernel.identity(atom).is_err());
    }

    #[test]
    fn copy_delete_and_free_reuse_follow_ephemeral_slot_semantics() {
        let Fixture { mut kernel, p, q } = fixture();
        let source = kernel.identity(p).unwrap();
        let reusable = kernel.identity(q).unwrap();
        assert!(kernel.remove_theorem(reusable));
        let target = kernel.copy_theorem(source).unwrap();
        assert_eq!(target, reusable);
        assert_eq!(
            kernel.require_thm(target).unwrap(),
            kernel.require_thm(source).unwrap()
        );
        assert!(kernel.remove_theorem(target));
        assert!(kernel.weaken(target, &[q], &[]).is_err());
        assert!(kernel.not_left(target, p).is_err());
        assert!(kernel.not_right(target, p).is_err());
        assert!(kernel.copy_theorem(target).is_err());
        assert_eq!(kernel.identity(q.negated()).unwrap(), target);
    }

    #[test]
    fn repeated_operands_support_idempotent_connective_rules() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(p)).unwrap());
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(p)).unwrap());
        let identity = kernel.identity(p).unwrap();
        let and_left = kernel.and_left(identity, conjunction).unwrap();
        let or_right = kernel.or_right(identity, disjunction).unwrap();
        assert_valid(&kernel, and_left, &[p, q]);
        assert_valid(&kernel, or_right, &[p, q]);
    }

    fn valid(sequent: ThmRef<'_>, p: Lit, p_value: bool, q: Lit, q_value: bool) -> bool {
        let value = |proposition: Lit| {
            let atom = if reference(proposition) == reference(p) {
                p_value
            } else {
                assert_eq!(reference(proposition), reference(q));
                q_value
            };
            if proposition.is_positive() {
                atom
            } else {
                !atom
            }
        };
        !sequent
            .lhs
            .rows()
            .all(|row| row.iter().copied().any(&value))
            || sequent
                .rhs
                .rows()
                .any(|row| row.iter().copied().all(&value))
    }

    fn assert_valid(kernel: &Kernel, theorem: ThmId, atoms: &[Lit]) {
        for mask in 0..(1_usize << atoms.len()) {
            let values: BTreeMap<_, _> = atoms
                .iter()
                .enumerate()
                .map(|(index, atom)| (reference(*atom), mask & (1 << index) != 0))
                .collect();
            let sequent = kernel.require_thm(theorem).unwrap();
            assert!(
                !sequent
                    .lhs
                    .rows()
                    .all(|row| row.iter().copied().any(|p| evaluate(kernel, p, &values)))
                    || sequent
                        .rhs
                        .rows()
                        .any(|row| row.iter().copied().all(|p| evaluate(kernel, p, &values))),
                "invalid sequent {sequent:?} under mask {mask}"
            );
        }
    }

    fn evaluate(kernel: &Kernel, proposition: Lit, atoms: &BTreeMap<Ref, bool>) -> bool {
        let reference = reference(proposition);
        let positive = if let Some(value) = kernel.arena().bool_value(reference) {
            value
        } else if let Some(op) = kernel.arena().op1(reference) {
            let child = kernel.arena().children(reference).unwrap().next().unwrap();
            match op {
                Op1::Not => !evaluate(kernel, positive(child), atoms),
            }
        } else if let Some(op) = kernel.arena().op2(reference) {
            let children: Vec<_> = kernel.arena().children(reference).unwrap().collect();
            let left = evaluate(kernel, positive(children[0]), atoms);
            let right = evaluate(kernel, positive(children[1]), atoms);
            match op {
                Op2::And => left && right,
                Op2::Or => left || right,
                Op2::Imp => !left || right,
            }
        } else {
            *atoms
                .get(&reference)
                .expect("test valuation covers every atom")
        };
        if proposition.is_positive() {
            positive
        } else {
            !positive
        }
    }
}
