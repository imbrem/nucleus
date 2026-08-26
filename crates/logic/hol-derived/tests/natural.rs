//! End-to-end coverage for the first userspace natural-number package.

use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, Ref, Sort};
use covalence_logic_hol_derived::{NaturalError, NaturalExt};

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
        .get(naturals.zero_member_theorem)
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
        (naturals.member_inhabited, naturals.member_inhabited_theorem),
        (naturals.rep_member, naturals.rep_member_theorem),
        (naturals.member_succ, naturals.member_succ_theorem),
        (naturals.induction, naturals.induction_theorem),
        (naturals.succ_injective, naturals.succ_injective_theorem),
        (naturals.zero_ne_succ, naturals.zero_ne_succ_theorem),
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
