//! End-to-end userspace projection of the axiom of infinity.

use covalence_logic_hol::{AX_INF, Kernel, Lit, Ref, Sort, Tag, TmTag, TyTag};
use covalence_logic_hol_derived::{
    ExistsError, InfinityError, InfinityExt, OpenedExistsDecl, forall_elim, open_exists,
    open_exists_at, substitute,
};

fn prelude() -> (Kernel, Ref) {
    let mut kernel = Kernel::new();
    let star = kernel.star().expect("star");
    let bool_ty = kernel.bool_ty(star).expect("bool");
    (kernel, bool_ty)
}

#[test]
fn infinity_projects_the_chosen_carrier_map_point_and_property() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    let package = kernel.choose_infinity(bool_ty).expect("infinity package");
    let declaration = package.declaration();
    let proof = package.proof();

    assert_eq!(kernel.category(package.carrier).expect("carrier"), Sort::Ty);
    assert_eq!(
        kernel.arena().tag(package.carrier),
        Some(Tag::Ty(TyTag::Model))
    );
    assert_eq!(kernel.category(package.map).expect("map"), Sort::Tm);
    assert_eq!(kernel.arena().tag(package.map), Some(Tag::Tm(TmTag::Eps)));
    assert_eq!(
        kernel.classifier(package.missed).expect("point"),
        package.carrier
    );
    assert_eq!(
        kernel.classifier(package.property).expect("property"),
        bool_ty
    );
    assert!(
        kernel
            .equivalent(package.model.specification, package.property)
            .expect("beta conversion union")
    );
    assert_eq!(declaration.carrier, package.carrier);
    assert_eq!(declaration.property, package.property);
    assert_eq!(proof.property, package.theorem);
    assert_eq!(proof.model.theorem, package.model.theorem);

    let theorem = kernel.thm().get(package.theorem).expect("property theorem");
    let rows = theorem.rhs.to_rows();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].as_slice(), [Lit::positive(package.property.get())]);
    assert_eq!(
        kernel
            .thm()
            .get(package.reflects_equality_theorem)
            .expect("reflection theorem")
            .rhs
            .to_rows()[0]
            .as_slice(),
        [Lit::positive(package.reflects_equality.get())]
    );
    assert_eq!(
        kernel
            .thm()
            .get(package.avoids_missed_theorem)
            .expect("missed-point theorem")
            .rhs
            .to_rows()[0]
            .as_slice(),
        [Lit::positive(package.avoids_missed.get())]
    );
    assert_eq!(
        kernel
            .thm()
            .get(package.model.theorem)
            .expect("chosen-model theorem")
            .rhs
            .to_rows()[0]
            .as_slice(),
        [Lit::positive(package.model.specification.get())]
    );
}

#[test]
fn projection_requires_exactly_the_infinity_capability() {
    let (mut kernel, bool_ty) = prelude();
    let before = kernel.arena().len();
    assert!(matches!(
        kernel.choose_infinity(bool_ty),
        Err(InfinityError::Kernel { .. })
    ));
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn exact_existential_opening_rejects_a_foreign_witness_before_mutation() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    let package = kernel.choose_infinity(bool_ty).expect("infinity package");
    let foreign = kernel.bool(bool_ty, true).expect("foreign witness");
    let before = kernel.arena().len();

    assert!(matches!(
        open_exists_at(
            &mut kernel,
            package.model.specification,
            OpenedExistsDecl {
                witness: foreign,
                body: package.missed_exists,
            },
        ),
        Err(ExistsError::WrongForm { reference })
            if reference == package.model.specification
    ));
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn an_invalid_exact_body_never_allocates_a_theorem() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    let package = kernel.choose_infinity(bool_ty).expect("infinity package");
    let foreign = kernel.bool(bool_ty, true).expect("foreign body");
    let theorem_count = kernel.thm().live_theorems().count();

    assert!(
        open_exists_at(
            &mut kernel,
            package.model.specification,
            OpenedExistsDecl {
                witness: package.map,
                body: foreign,
            },
        )
        .is_err()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn explicit_binder_replay_is_independent_of_the_ambient_suffix() {
    let (mut first, bool_ty) = prelude();
    first.add_axiom(AX_INF).expect("infinity capability");
    let selected = first
        .choose_infinity_at(bool_ty, 100)
        .expect("explicit selection");

    let (mut second, second_bool) = prelude();
    second.add_axiom(AX_INF).expect("infinity capability");
    for name in 1..20 {
        second.tm_fv(name, second_bool).expect("ambient suffix");
    }
    let replayed = second
        .choose_infinity_at(second_bool, 100)
        .expect("replayed selection");

    assert_eq!(selected.axiom.base_name, replayed.axiom.base_name);
    assert_eq!(selected.axiom.carrier_name, replayed.axiom.carrier_name);
    assert_eq!(
        first.arena().name(selected.axiom.exists_type),
        second.arena().name(replayed.axiom.exists_type)
    );
}

#[test]
fn infinity_reflection_specializes_through_standard_hol_rules() {
    let (mut kernel, bool_ty) = prelude();
    kernel.add_axiom(AX_INF).expect("infinity capability");
    let package = kernel.choose_infinity(bool_ty).expect("infinity package");

    let at_left = forall_elim(
        &mut kernel,
        package.reflects_equality_theorem,
        package.missed,
    )
    .expect("first universal elimination");
    let at_both = forall_elim(&mut kernel, at_left.theorem, package.missed)
        .expect("second universal elimination");

    assert_eq!(
        kernel.classifier(at_both.proposition).expect("Boolean"),
        bool_ty
    );
    let theorem = kernel.thm().get(at_both.theorem).expect("exact theorem");
    assert!(theorem.lhs.rows().next().is_none());
    let rows = theorem.rhs.to_rows();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0].as_slice(),
        [Lit::positive(at_both.proposition.get())]
    );
}

#[test]
fn public_substitution_and_existential_opening_are_checked_utilities() {
    let (mut kernel, bool_ty) = prelude();
    let variable = kernel.tm_fv(0, bool_ty).expect("variable");
    let truth = kernel.bool(bool_ty, true).expect("truth");
    let body = kernel.eq(bool_ty, variable, truth).expect("body");
    let existential = kernel.exists_tm(variable, body).expect("exists");
    let opened = open_exists(&mut kernel, existential).expect("open exists");
    assert!(
        kernel
            .equivalent(existential, opened.body)
            .expect("equivalent")
    );

    // Term substitution crosses a type binder without confusing namespaces.
    let quantified = kernel.ty_forall(0, body).expect("type universal");
    let result = substitute(&mut kernel, variable, truth, quantified).expect("substitution");
    assert_eq!(
        kernel.arena().tag(result.output),
        Some(Tag::Tm(TmTag::TyForall))
    );
}
