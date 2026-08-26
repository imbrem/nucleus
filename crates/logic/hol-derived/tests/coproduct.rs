use covalence_logic_hol::{AX_SUB, Kernel, Sort};
use covalence_logic_hol_derived::CoproductExt;

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
