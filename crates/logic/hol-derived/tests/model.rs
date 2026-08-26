//! End-to-end userspace opening of type-existential model packages.

use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, Lit, Ref, Sort, SynRel, Tag};
use covalence_logic_hol_derived::{ModelError, ModelExt, join_same_syntax, substitute};

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
    let declaration = chosen.declaration();
    let proof = chosen.proof();
    assert_eq!(chosen.name, axiom.model_name);
    assert_eq!(chosen.predicate, axiom.package_body);
    assert_eq!(kernel.category(chosen.ty).expect("model type"), Sort::Ty);
    assert_eq!(
        kernel.arena().tag(chosen.ty),
        Some(Tag::Ty(covalence_logic_hol::TyTag::Model))
    );
    assert_specification_theorem(&kernel, chosen.theorem, chosen.specification);
    assert_eq!(declaration.ty, chosen.ty);
    assert_eq!(declaration.specification, chosen.specification);
    assert_eq!(proof.theorem, chosen.theorem);
    assert_eq!(proof.substitution, chosen.substitution);

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

#[test]
fn substitution_certifies_rebuilt_duplicate_classifier_rows_on_demand() {
    let (mut kernel, star, bool_ty) = prelude();
    let parameter = kernel.ty_fv(1, star).expect("type parameter");
    let left_arrow = kernel.ty_arr(parameter, parameter).expect("left arrow");
    let right_arrow = kernel.ty_arr(parameter, parameter).expect("right arrow");
    join_same_syntax(&mut kernel, left_arrow, right_arrow).expect("source classifier equality");
    let function_ty = kernel
        .ty_arr(left_arrow, bool_ty)
        .expect("higher-order function type");
    let function = kernel.tm_fv(2, function_ty).expect("function");
    let argument = kernel.tm_fv(3, right_arrow).expect("argument");
    let application = kernel.app(function, argument).expect("source application");

    let rebuilt = substitute(&mut kernel, parameter, bool_ty, application)
        .expect("checked classifier retry")
        .output;
    assert_eq!(kernel.classifier(rebuilt).expect("Boolean result"), bool_ty);
}
