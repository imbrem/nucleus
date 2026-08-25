//! The axiom of infinity: its sentence and capability boundary.

mod support;

use covalence_logic_hol::{AX_INF, AX_SUB, InfinityBinder, KernelError, Lit, Sort};
use support::Fix;

#[test]
fn concluding_infinity_requires_its_own_capability() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    assert!(matches!(
        fix.kernel.inf_exists(bool_ty),
        Err(KernelError::MissingAxiom { name: AX_INF })
    ));

    // `ax.sub` does not license `ax.inf`: the capabilities are separate.
    fix.kernel.add_axiom(AX_SUB).expect("subtype capability");
    assert!(matches!(
        fix.kernel.inf_exists(bool_ty),
        Err(KernelError::MissingAxiom { name: AX_INF })
    ));
}

#[test]
fn the_infinity_sentence_is_a_closed_proposition() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    fix.kernel.add_axiom(AX_INF).expect("capability");
    let axiom = fix.kernel.inf_exists(bool_ty).expect("axiom");

    assert_eq!(
        fix.kernel.category(axiom.exists_type).expect("sentence"),
        Sort::Tm
    );
    let classifier = fix
        .kernel
        .classifier(axiom.exists_type)
        .expect("classifier");
    assert!(
        fix.kernel
            .equivalent(classifier, bool_ty)
            .expect("equivalent"),
        "the infinity sentence is Boolean"
    );
    assert_eq!(axiom.carrier_name, axiom.name_of(InfinityBinder::Carrier));

    let sequent = fix.kernel.thm().get(axiom.theorem).expect("sequent");
    assert!(
        sequent.lhs.to_rows().is_empty(),
        "the axiom is premise-free"
    );
    assert_eq!(
        sequent.rhs.to_rows()[0].as_slice(),
        [Lit::positive(axiom.exists_type.get())]
    );
}

#[test]
fn the_body_and_carrier_name_determine_the_chosen_model_syntax() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    fix.kernel.add_axiom(AX_INF).expect("capability");
    let axiom = fix.kernel.inf_exists(bool_ty).expect("axiom");

    let chosen = fix
        .kernel
        .model(axiom.carrier_name, axiom.body)
        .expect("chosen carrier syntax");
    assert_eq!(fix.kernel.category(chosen).expect("model"), Sort::Ty);
}
