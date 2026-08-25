//! End-to-end userspace projection of the axiom of infinity.

use covalence_logic_hol::{AX_INF, Kernel, Lit, Ref, Sort, Tag, TmTag, TyTag};
use covalence_logic_hol_derived::{InfinityError, InfinityExt, open_exists, substitute};

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

    let theorem = kernel.thm().get(package.theorem).expect("specification");
    let rows = theorem.rhs.to_rows();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0].as_slice(),
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
