use covalence_logic_hol::{AX_SUB, Kernel, Sort};
use covalence_logic_hol_derived::{CoproductExt, join_same_syntax};

#[test]
fn guarded_coproduct_has_checked_carrier_type_and_injections() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();

    let coproduct = kernel.coproduct(bool_ty, bool_ty, right).unwrap();

    assert_eq!(kernel.category(coproduct.ty).unwrap(), Sort::Ty);
    assert_eq!(kernel.classifier(coproduct.inl).unwrap(), coproduct.inl_ty);
    assert_eq!(kernel.classifier(coproduct.inr).unwrap(), coproduct.inr_ty);
    assert_eq!(coproduct.subtype.sub, coproduct.ty);
    assert!(coproduct.subtype.theorem().is_some());
}

#[test]
fn coproduct_terms_need_no_capability_and_failure_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();

    let terms = kernel.coproduct_terms(bool_ty, bool_ty, bool_ty).unwrap();
    assert!(terms.subtype.theorem().is_none());

    let truth = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().clone();
    assert!(kernel.coproduct(bool_ty, truth, bool_ty).is_err());
    assert_eq!(*kernel.arena(), before);
}

#[test]
fn eliminator_is_checked_at_each_requested_codomain() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let codomain = kernel.ty_arr(bool_ty, bool_ty).unwrap();

    let eliminator = coproduct.eliminator(&mut kernel, codomain).unwrap();

    assert_eq!(
        kernel.classifier(eliminator.function).unwrap(),
        eliminator.function_ty
    );
    let left = kernel.tm_fv(100, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(101, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(102, coproduct.ty).unwrap();
    let applied = kernel.app(eliminator.function, left).unwrap();
    let applied = kernel.app(applied, right).unwrap();
    let applied = kernel.app(applied, value).unwrap();
    assert_eq!(kernel.classifier(applied).unwrap(), codomain);
}

#[test]
fn left_computation_is_an_exact_premise_free_theorem() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(200, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(201, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(202, coproduct.left).unwrap();
    let injected = kernel.app(coproduct.inl, value).unwrap();
    let direct = kernel.app(eliminator.function, left).unwrap();
    let direct = kernel.app(direct, right).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(left, value).unwrap();
    let expected_proposition = kernel.eq(bool_ty, direct, expected).unwrap();

    let computation = coproduct
        .prove_case_inl(&mut kernel, eliminator, left, right, value)
        .unwrap();

    let theorem = kernel.thm().get(computation.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    let rows = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0],
        &[covalence_logic_hol::Lit::positive(
            computation.proposition.get()
        )]
    );
    join_same_syntax(&mut kernel, computation.proposition, expected_proposition).unwrap();
}

#[test]
fn right_computation_is_an_exact_premise_free_theorem() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(300, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(301, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(302, coproduct.right).unwrap();
    let injected = kernel.app(coproduct.inr, value).unwrap();
    let direct = kernel.app(eliminator.function, left).unwrap();
    let direct = kernel.app(direct, right).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(right, value).unwrap();
    let expected_proposition = kernel.eq(bool_ty, direct, expected).unwrap();

    let computation = coproduct
        .prove_case_inr(&mut kernel, eliminator, left, right, value)
        .unwrap();

    let theorem = kernel.thm().get(computation.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    let rows = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0],
        &[covalence_logic_hol::Lit::positive(
            computation.proposition.get()
        )]
    );
    join_same_syntax(&mut kernel, computation.proposition, expected_proposition).unwrap();
}

#[test]
fn computation_rejection_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, bool_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(400, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(401, eliminator.right_map_ty).unwrap();
    let wrong_value = kernel.tm_fv(402, eliminator.left_map_ty).unwrap();
    let before = kernel.arena().clone();

    assert!(
        coproduct
            .prove_case_inl(&mut kernel, eliminator, left, right, wrong_value)
            .is_err()
    );
    assert_eq!(*kernel.arena(), before);
}
