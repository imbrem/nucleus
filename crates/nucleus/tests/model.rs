//! End-to-end userspace opening of type-existential model packages.

use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, Lit, Ref, Sort, SynRel, Tag};
use covalence_nucleus::{ModelError, ModelExt};

fn prelude() -> (Kernel, Ref, Ref) {
    let mut kernel = Kernel::new();
    let star = kernel.star().expect("star");
    let bool_ty = kernel.bool_ty(star).expect("bool");
    (kernel, star, bool_ty)
}

fn assert_specification_theorem(kernel: &Kernel, theorem: covalence_logic_hol::ThmId, term: Ref) {
    let sequent = kernel.thm().get(theorem).expect("specification theorem");
    assert!(sequent.lhs.rows().next().is_none());
    let rows: Vec<_> = sequent.rhs.rows().collect();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0], [Lit::positive(term.get())]);
}

#[test]
fn subtype_package_opens_at_the_exact_model_chosen_by_its_existential() {
    let (mut kernel, _star, bool_ty) = prelude();
    let variable = kernel.tm_fv(0, bool_ty).expect("variable");
    let predicate = kernel.lam(variable, variable).expect("predicate");
    kernel.add_axiom(AX_SUB).expect("subtype capability");
    let axiom = kernel
        .sub_exists(bool_ty, bool_ty, predicate)
        .expect("subtype package");
    let chosen = kernel.choose_model(axiom.theorem).expect("chosen model");
    assert_eq!(chosen.name, axiom.model_name);
    assert_eq!(chosen.predicate, axiom.package_body);
    assert_eq!(kernel.category(chosen.ty).expect("model type"), Sort::Ty);
    assert_eq!(
        kernel.arena().tag(chosen.ty),
        Some(Tag::Ty(covalence_logic_hol::TyTag::Model))
    );
    assert_specification_theorem(&kernel, chosen.theorem, chosen.specification);

    let fact = kernel
        .arena()
        .syn_fact(chosen.substitution)
        .expect("substitution fact");
    assert_eq!(fact.rel(), SynRel::Syn);
    assert_eq!(fact.input(), axiom.package_body);
    assert_eq!(fact.output(), chosen.specification);
}

#[test]
fn the_full_infinity_body_can_be_opened_in_userspace() {
    let (mut kernel, _star, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    let infinity = kernel.inf_exists(bool_ty).expect("infinity package");

    let chosen = kernel
        .choose_model(infinity.theorem)
        .expect("the recursive certificate reaches every retyped term");
    assert_eq!(chosen.name, infinity.carrier_name);
    assert_eq!(chosen.predicate, infinity.body);
    assert_eq!(
        kernel.classifier(chosen.specification).expect("Boolean"),
        bool_ty
    );
    assert_specification_theorem(&kernel, chosen.theorem, chosen.specification);
}

#[test]
fn a_non_existential_theorem_is_rejected_before_model_construction() {
    let (mut kernel, _star, bool_ty) = prelude();
    let truth = kernel.bool(bool_ty, true).expect("truth");
    let theorem = kernel
        .identity(Lit::positive(truth.get()))
        .expect("identity");
    let before = kernel.arena().len();

    assert!(matches!(
        kernel.choose_model(theorem),
        Err(ModelError::WrongTheorem { theorem: rejected }) if rejected == theorem
    ));
    assert_eq!(
        kernel.arena().len(),
        before,
        "shape rejection is non-mutating"
    );
}
