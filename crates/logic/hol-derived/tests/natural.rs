//! End-to-end coverage for the first userspace natural-number package.

use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, Lit, Ref, Sort, builtin::Op2};
use covalence_logic_hol_derived::{NaturalError, NaturalExt, substitute};

fn prelude() -> (Kernel, Ref) {
    let mut kernel = Kernel::new();
    let star = kernel.star().expect("star");
    let bool_ty = kernel.bool_ty(star).expect("bool");
    (kernel, bool_ty)
}

#[test]
fn naturals_are_carved_from_infinity_with_only_the_two_named_capabilities() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    kernel.add_axiom(AX_SUB).expect("subtype capability");
    let naturals = kernel.choose_naturals(bool_ty).expect("naturals");

    assert_eq!(kernel.category(naturals.ty).expect("nat type"), Sort::Ty);
    assert_eq!(kernel.classifier(naturals.zero).expect("zero"), naturals.ty);
    let succ_ty = kernel.classifier(naturals.succ).expect("successor");
    let mut succ_parts = kernel.arena().children(succ_ty).expect("arrow children");
    assert_eq!(succ_parts.next(), Some(naturals.ty));
    assert_eq!(succ_parts.next(), Some(naturals.ty));
    assert_eq!(
        kernel.classifier(naturals.induction).expect("induction"),
        bool_ty
    );
    assert_eq!(naturals.subtype.carrier, naturals.infinity.carrier);
    assert_eq!(naturals.subtype.predicate, naturals.member);
    assert!(naturals.subtype.theorem().is_some());
    assert_eq!(naturals.get("nat"), Some(naturals.ty));
    assert_eq!(naturals.get("nat.zero"), Some(naturals.zero));
    assert_eq!(naturals.get("nat.succ"), Some(naturals.succ));
    assert_eq!(naturals.get("nat.zero_member"), Some(naturals.zero_member));
    let theorem = kernel
        .thm()
        .get(naturals.proof.zero_member)
        .expect("zero membership theorem");
    assert!(theorem.lhs.rows().next().is_none());
    let conclusions = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(conclusions.len(), 1);
    assert_eq!(conclusions[0].len(), 1);
    assert!(conclusions[0][0].is_positive());
    assert_eq!(
        conclusions[0][0].magnitude(),
        naturals.zero_member.get().cast_unsigned()
    );
    assert_eq!(
        naturals.get("nat.member_inhabited"),
        Some(naturals.member_inhabited)
    );
    assert_eq!(naturals.get("nat.rep_member"), Some(naturals.rep_member));
    for (proposition, theorem) in [
        (naturals.member_inhabited, naturals.proof.member_inhabited),
        (naturals.rep_member, naturals.proof.rep_member),
        (naturals.member_succ, naturals.proof.member_succ),
        (naturals.induction, naturals.proof.induction),
        (naturals.succ_injective, naturals.proof.succ_injective),
        (naturals.zero_ne_succ, naturals.proof.zero_ne_succ),
    ] {
        let theorem = kernel.thm().get(theorem).expect("derived exact theorem");
        assert!(theorem.lhs.rows().next().is_none());
        let rows = theorem.rhs.rows().collect::<Vec<_>>();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].len(), 1);
        assert!(rows[0][0].is_positive());
        assert_eq!(rows[0][0].magnitude(), proposition.get().cast_unsigned());
    }
    assert_eq!(naturals.get("nat.member_succ"), Some(naturals.member_succ));
    assert_eq!(naturals.symbols().len(), 16);
    assert_eq!(naturals.get("nat.rec"), None);
    assert_eq!(
        kernel.arena().axioms().collect::<Vec<_>>(),
        [AX_INF, AX_SUB]
    );
}

#[test]
fn missing_either_capability_is_rejected_before_mutation() {
    for capability in [None, Some(AX_INF), Some(AX_SUB)] {
        let (mut kernel, bool_ty) = prelude();
        if let Some(capability) = capability {
            kernel.add_axiom(capability).expect("known capability");
        }
        let before = kernel.arena().clone();
        assert!(matches!(
            kernel.choose_naturals(bool_ty),
            Err(NaturalError::Kernel { .. })
        ));
        assert_eq!(*kernel.arena(), before);
    }
}

#[test]
fn construction_is_deterministic() {
    let build = || {
        let (mut kernel, bool_ty) = prelude();
        kernel.add_axiom(AX_INF).expect("infinity capability");
        kernel.add_axiom(AX_SUB).expect("subtype capability");
        let naturals = kernel.choose_naturals(bool_ty).expect("naturals");
        (
            kernel.arena().addr(),
            naturals.ty,
            naturals.zero,
            naturals.succ,
        )
    };
    assert_eq!(build(), build());
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn prove_constant_true(
    kernel: &mut Kernel,
    predicate: Ref,
    binder: Ref,
    argument: Ref,
    truth: Ref,
) -> (Ref, covalence_logic_hol::ThmId) {
    let application = kernel
        .app(predicate, argument)
        .expect("predicate application");
    let substitution = substitute(kernel, binder, argument, truth).expect("constant substitution");
    let beta = kernel
        .tm_beta_fact(None, application, substitution.fact)
        .expect("beta fact");
    kernel.union_syn_fact(beta).expect("register beta fact");
    let theorem = kernel.true_right(positive(truth)).expect("truth theorem");
    kernel
        .convert_conclusions(theorem, truth, application)
        .expect("convert truth to constant predicate");
    (application, theorem)
}

#[test]
fn induction_is_a_transactional_userspace_combinator() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    kernel.add_axiom(AX_SUB).expect("subtype capability");
    let naturals = kernel.choose_naturals(bool_ty).expect("naturals");
    let truth = kernel.bool(bool_ty, true).expect("truth");
    let induction_function = kernel
        .arena()
        .children(naturals.induction)
        .expect("induction equality")
        .nth(1)
        .expect("induction function");
    let induction_predicate = kernel
        .arena()
        .children(induction_function)
        .expect("induction lambda")
        .next()
        .expect("induction predicate");
    let predicate_ty = kernel
        .classifier(induction_predicate)
        .expect("predicate type");
    let binder = kernel
        .tm_fv(
            kernel.fresh_name(&[naturals.ty]).expect("fresh name"),
            naturals.ty,
        )
        .expect("binder");
    let predicate = kernel
        .lam_at(predicate_ty, binder, truth)
        .expect("constant predicate");

    let (_, base) = prove_constant_true(&mut kernel, predicate, binder, naturals.zero, truth);
    let step_binder = kernel
        .tm_fv(
            kernel.fresh_name(&[predicate]).expect("fresh step name"),
            naturals.ty,
        )
        .expect("step binder");
    let next = kernel
        .app(naturals.succ, step_binder)
        .expect("successor application");
    let at_step = kernel.app(predicate, step_binder).expect("step antecedent");
    let (at_next, next_truth) = prove_constant_true(&mut kernel, predicate, binder, next, truth);
    let step_implication = kernel
        .op2(Op2::Imp, at_step, at_next)
        .expect("step implication");
    kernel
        .weaken(next_truth, &[positive(at_step)], &[])
        .expect("step hypothesis");
    let step = kernel
        .imp_right(next_truth, positive(step_implication))
        .expect("step implication introduction");
    let step = kernel
        .forall_intro(step, step_binder)
        .expect("step universal introduction");

    let induction = naturals
        .induct(&mut kernel, predicate, base, step.theorem)
        .expect("induction");
    let theorem = kernel.thm().get(induction.theorem).expect("result theorem");
    assert!(theorem.lhs.rows().next().is_none());
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[positive(induction.universal)][..]]
    );

    let contextual = kernel.identity(positive(induction.base)).expect("identity");
    let before = kernel.arena().clone();
    assert!(matches!(
        naturals.induct(&mut kernel, predicate, contextual, step.theorem),
        Err(NaturalError::WrongForm { .. })
    ));
    assert_eq!(*kernel.arena(), before);
}
