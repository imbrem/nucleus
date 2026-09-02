//! Polymorphic conditionals derived from equality, Boolean connectives, and choice.
//!
//! This adds no syntax tag, axiom, or trusted theorem rule. A conditional over
//! `A` is Hilbert choice from
//! `λz. (condition = true ∧ z = then) ∨ (condition = false ∧ z = else)`.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, ThmId, builtin::Op2};

use crate::{ExistsError, ModelError, SyntaxError, introduce_exists, join_same_syntax, substitute};

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

/// Exact checked syntax for one polymorphic conditional.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Conditional {
    /// Result type shared by the binder and both branches.
    pub ty: Ref,
    /// Boolean selector.
    pub condition: Ref,
    /// Value selected when the condition holds.
    pub then_branch: Ref,
    /// Value selected when the condition does not hold.
    pub else_branch: Ref,
    /// Caller-supplied variable bound in the graph predicate.
    pub binder: Ref,
    /// Graph equality for the true branch.
    pub then_equality: Ref,
    /// Graph equality for the false branch.
    pub else_equality: Ref,
    /// Equality between the condition and truth.
    pub condition_true: Ref,
    /// Equality between the condition and falsehood.
    pub condition_false: Ref,
    /// Conjunctive true branch of the graph.
    pub true_case: Ref,
    /// Conjunctive false branch of the graph.
    pub false_case: Ref,
    /// Disjunctive graph body.
    pub body: Ref,
    /// Lambda abstraction of the graph body.
    pub predicate: Ref,
    /// Hilbert-choice result selected from the graph.
    pub term: Ref,
}

/// A conditional construction or checked branch proof was rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConditionalError {
    /// A checked kernel operation rejected the derived step.
    #[snafu(display("conditional construction was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The graph witness could not be introduced as a Hilbert choice.
    #[snafu(display("conditional choice introduction failed: {source}"))]
    Choice {
        /// Underlying choice-introduction failure.
        source: ExistsError,
    },
    /// Two checked rows could not be certified as structurally identical.
    #[snafu(display("conditional syntax certification failed: {source}"))]
    Syntax {
        /// Underlying structural certification failure.
        source: SyntaxError,
    },
    /// Capture-avoiding substitution into the graph body could not be derived.
    #[snafu(display("conditional substitution failed: {source}"))]
    Substitution {
        /// Underlying capture-avoiding substitution failure.
        source: ModelError,
    },
}

impl From<KernelError> for ConditionalError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<ExistsError> for ConditionalError {
    fn from(source: ExistsError) -> Self {
        Self::Choice { source }
    }
}

impl From<SyntaxError> for ConditionalError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

impl From<ModelError> for ConditionalError {
    fn from(source: ModelError) -> Self {
        Self::Substitution { source }
    }
}

/// Builds a typed HOL conditional as a Hilbert-choice graph.
///
/// The caller supplies the predicate binder so naming and capture policy stay
/// outside the kernel. The construction is transactional.
///
/// # Errors
///
/// Returns an error unless `condition` is Boolean, `binder` and both branches
/// have type `ty`, and every checked constructor accepts the rows.
pub fn conditional(
    kernel: &mut Kernel,
    bool_ty: Ref,
    ty: Ref,
    binder: Ref,
    condition: Ref,
    then_branch: Ref,
    else_branch: Ref,
) -> Result<Conditional, ConditionalError> {
    let mut staged = kernel.fork();
    let then_equality = staged.eq(bool_ty, binder, then_branch)?;
    let else_equality = staged.eq(bool_ty, binder, else_branch)?;
    let truth = staged.bool(bool_ty, true)?;
    let falsehood = staged.bool(bool_ty, false)?;
    let condition_true = staged.eq(bool_ty, condition, truth)?;
    let condition_false = staged.eq(bool_ty, condition, falsehood)?;
    let true_case = staged.op2(Op2::And, condition_true, then_equality)?;
    let false_case = staged.op2(Op2::And, condition_false, else_equality)?;
    let body = staged.op2(Op2::Or, true_case, false_case)?;
    let predicate = staged.lam(binder, body)?;
    let term = staged.eps(ty, predicate)?;
    let result = Conditional {
        ty,
        condition,
        then_branch,
        else_branch,
        binder,
        then_equality,
        else_equality,
        condition_true,
        condition_false,
        true_case,
        false_case,
        body,
        predicate,
        term,
    };
    *kernel = staged;
    Ok(result)
}

/// Proves `condition = true ⊢ conditional = then_branch`.
///
/// # Errors
///
/// Returns an error unless `conditional` has the checked shape produced by
/// [`conditional`] and all ordinary proof and syntax checks succeed.
pub fn conditional_when_true(
    kernel: &mut Kernel,
    bool_ty: Ref,
    conditional: Conditional,
) -> Result<ThmId, ConditionalError> {
    branch_law(kernel, bool_ty, conditional, true)
}

/// Proves `condition = false ⊢ conditional = else_branch`.
///
/// # Errors
///
/// Returns an error under the same conditions as [`conditional_when_true`].
pub fn conditional_when_false(
    kernel: &mut Kernel,
    bool_ty: Ref,
    conditional: Conditional,
) -> Result<ThmId, ConditionalError> {
    branch_law(kernel, bool_ty, conditional, false)
}

fn branch_law(
    kernel: &mut Kernel,
    bool_ty: Ref,
    conditional: Conditional,
    when_true: bool,
) -> Result<ThmId, ConditionalError> {
    let mut staged = kernel.fork();
    let theorem = branch_law_inner(&mut staged, bool_ty, conditional, when_true)?;
    *kernel = staged;
    Ok(theorem)
}

#[allow(clippy::too_many_lines)]
fn branch_law_inner(
    kernel: &mut Kernel,
    bool_ty: Ref,
    conditional: Conditional,
    when_true: bool,
) -> Result<ThmId, ConditionalError> {
    let selected = if when_true {
        conditional.then_branch
    } else {
        conditional.else_branch
    };
    let witness_then_equality = kernel.eq(bool_ty, selected, conditional.then_branch)?;
    let witness_else_equality = kernel.eq(bool_ty, selected, conditional.else_branch)?;
    let witness_true_case =
        kernel.op2(Op2::And, conditional.condition_true, witness_then_equality)?;
    let witness_false_case =
        kernel.op2(Op2::And, conditional.condition_false, witness_else_equality)?;
    let witness_body = kernel.op2(Op2::Or, witness_true_case, witness_false_case)?;
    let selected_equality = if when_true {
        witness_then_equality
    } else {
        witness_else_equality
    };
    let selected_refl = kernel.refl(bool_ty, selected)?;
    join_same_syntax(kernel, selected_refl.equality, selected_equality)?;
    kernel.convert_conclusions(
        selected_refl.theorem,
        selected_refl.equality,
        selected_equality,
    )?;

    let branch_assumption = if when_true {
        conditional.condition_true
    } else {
        conditional.condition_false
    };
    let assumption = kernel.identity(positive(branch_assumption))?;
    let witness_case = kernel.and_right(
        assumption,
        selected_refl.theorem,
        positive(if when_true {
            witness_true_case
        } else {
            witness_false_case
        }),
    )?;
    kernel.weaken(
        witness_case,
        &[],
        &[positive(if when_true {
            witness_false_case
        } else {
            witness_true_case
        })],
    )?;
    let witness_body = kernel.or_right(witness_case, positive(witness_body))?;
    let choice = introduce_exists(
        kernel,
        witness_body,
        conditional.binder,
        conditional.body,
        selected,
    )?;
    let result_equality = kernel.eq(bool_ty, conditional.term, selected)?;
    let selected_case = kernel.identity(positive(result_equality))?;
    kernel.weaken(selected_case, &[positive(branch_assumption)], &[])?;
    let selected_conjunction = kernel.op2(Op2::And, branch_assumption, result_equality)?;
    let selected_case = kernel.and_left(selected_case, positive(selected_conjunction))?;

    let other_branch = if when_true {
        conditional.else_branch
    } else {
        conditional.then_branch
    };
    let other_equality = kernel.eq(bool_ty, conditional.term, other_branch)?;
    let term_then_equality = if when_true {
        result_equality
    } else {
        other_equality
    };
    let term_else_equality = if when_true {
        other_equality
    } else {
        result_equality
    };
    let term_true_case = kernel.op2(Op2::And, conditional.condition_true, term_then_equality)?;
    let term_false_case = kernel.op2(Op2::And, conditional.condition_false, term_else_equality)?;
    let target_proposition = kernel.op2(Op2::Or, term_true_case, term_false_case)?;
    let application = kernel.app(conditional.predicate, conditional.term)?;
    join_same_syntax(kernel, choice.proposition, application)?;
    let substitution = substitute(
        kernel,
        conditional.binder,
        conditional.term,
        conditional.body,
    )?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    join_same_syntax(kernel, substitution.output, target_proposition)?;
    kernel.convert_conclusions(choice.theorem, choice.proposition, target_proposition)?;
    let true_condition = kernel.identity(positive(conditional.condition_true))?;
    let true_condition = kernel.eqt_elim(true_condition)?;
    let false_condition = kernel.identity(positive(conditional.condition_false))?;
    let contradiction = kernel.eq_mp(false_condition, true_condition)?;
    let falsehood = kernel
        .arena()
        .children(conditional.condition_false)
        .and_then(|mut children| children.nth(2))
        .ok_or(ConditionalError::Kernel {
            source: KernelError::InvalidTheoremRule {
                rule: "conditional false branch",
            },
        })?;
    let contradiction = kernel.flatten_conclusion(contradiction, positive(falsehood))?;
    kernel.weaken(
        contradiction,
        &[positive(other_equality)],
        &[positive(result_equality)],
    )?;
    let other_assumption = if when_true {
        conditional.condition_false
    } else {
        conditional.condition_true
    };
    let other_conjunction = kernel.op2(Op2::And, other_assumption, other_equality)?;
    let impossible_case = kernel.and_left(contradiction, positive(other_conjunction))?;

    let selected_target = if when_true {
        term_true_case
    } else {
        term_false_case
    };
    join_same_syntax(kernel, selected_conjunction, selected_target)?;
    kernel.convert_theorem(selected_case, selected_conjunction, selected_target)?;
    let other_target = if when_true {
        term_false_case
    } else {
        term_true_case
    };
    join_same_syntax(kernel, other_conjunction, other_target)?;
    kernel.convert_theorem(impossible_case, other_conjunction, other_target)?;

    let (true_elim, false_elim) = if when_true {
        (selected_case, impossible_case)
    } else {
        (impossible_case, selected_case)
    };
    let eliminate = kernel.or_left(true_elim, false_elim, positive(target_proposition))?;
    let result = kernel.cut(choice.theorem, eliminate, positive(target_proposition))?;
    kernel.contract_theorem(result)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Kernel, Ref, Ref, Ref, Ref, Ref, Ref) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let condition = kernel.tm_fv(1, bool_ty).unwrap();
        let ty = kernel.ty_fv(2, star).unwrap();
        let then_branch = kernel.tm_fv(3, ty).unwrap();
        let else_branch = kernel.tm_fv(4, ty).unwrap();
        let binder = kernel.tm_fv(5, ty).unwrap();
        (
            kernel,
            bool_ty,
            ty,
            binder,
            condition,
            then_branch,
            else_branch,
        )
    }

    #[test]
    fn conditional_is_typed_and_both_branch_laws_are_checked() {
        let (mut kernel, bool_ty, ty, binder, condition, then_branch, else_branch) = fixture();
        let conditional = conditional(
            &mut kernel,
            bool_ty,
            ty,
            binder,
            condition,
            then_branch,
            else_branch,
        )
        .unwrap();
        assert_eq!(kernel.classifier(conditional.term).unwrap(), ty);
        let when_true = conditional_when_true(&mut kernel, bool_ty, conditional).unwrap();
        let when_false = conditional_when_false(&mut kernel, bool_ty, conditional).unwrap();
        assert_branch_law(
            &kernel,
            when_true,
            conditional.condition_true,
            conditional.term,
            then_branch,
        );
        assert_branch_law(
            &kernel,
            when_false,
            conditional.condition_false,
            conditional.term,
            else_branch,
        );
    }

    #[test]
    fn malformed_branch_sort_is_transactional() {
        let (mut kernel, bool_ty, ty, binder, condition, then_branch, _) = fixture();
        let before = kernel.arena().clone();
        assert!(
            conditional(
                &mut kernel,
                bool_ty,
                ty,
                binder,
                condition,
                then_branch,
                condition,
            )
            .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }

    #[test]
    fn malformed_branch_law_is_transactional() {
        let (mut kernel, bool_ty, ty, binder, condition, then_branch, else_branch) = fixture();
        let conditional = conditional(
            &mut kernel,
            bool_ty,
            ty,
            binder,
            condition,
            then_branch,
            else_branch,
        )
        .unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let forged = Conditional {
            body: truth,
            ..conditional
        };
        let before = kernel.arena().clone();

        assert!(conditional_when_true(&mut kernel, bool_ty, forged).is_err());
        assert_eq!(kernel.arena(), &before);
        assert!(conditional_when_false(&mut kernel, bool_ty, forged).is_err());
        assert_eq!(kernel.arena(), &before);
    }

    fn assert_branch_law(
        kernel: &Kernel,
        theorem: ThmId,
        premise: Ref,
        conditional: Ref,
        branch: Ref,
    ) {
        let theorem = kernel.thm().get(theorem).unwrap();
        let premises = theorem.lhs.to_rows();
        assert_eq!(premises.len(), 1);
        assert_eq!(premises[0].as_slice(), [positive(premise)]);
        let conclusions = theorem.rhs.to_rows();
        let [row] = conclusions.as_slice() else {
            panic!("branch law must conclude one equality");
        };
        let [equality] = row.as_slice() else {
            panic!("branch law must conclude one equality");
        };
        let children = kernel
            .arena()
            .children(Ref::new(i32::try_from(equality.magnitude()).unwrap()).unwrap())
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(children[1..], [conditional, branch]);
    }
}
