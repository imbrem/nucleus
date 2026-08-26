//! The untrusted guarded-subtype layer over the subtype axiom.

use std::collections::BTreeSet;

use covalence_logic_hol::{AX_SUB, Binder, Kernel, KernelError, Lit, Ref, Sort, Table, ThmId};
use covalence_logic_hol_derived::{Subtype, SubtypeError, SubtypeExt};

/// A kernel with `star`, `bool`, a carrier, and a predicate over it.
struct Fix {
    kernel: Kernel,
    bool_ty: Ref,
    carrier: Ref,
    predicate: Ref,
}

impl Fix {
    /// Carrier `bool`, predicate `λx. x`.
    fn identity_on_bool() -> Self {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let bool_ty = kernel.bool_ty(star).expect("bool");
        let variable = kernel.tm_fv(0, bool_ty).expect("binder");
        let predicate = kernel.lam(variable, variable).expect("predicate");
        Self {
            kernel,
            bool_ty,
            carrier: bool_ty,
            predicate,
        }
    }

    fn licensed(mut self) -> Self {
        self.kernel.add_axiom(AX_SUB).expect("capability");
        self
    }

    fn guarded(&mut self) -> Result<Subtype, SubtypeError> {
        self.kernel
            .guarded_subtype(self.bool_ty, self.carrier, self.predicate)
    }
}

/// Structural equality over two rows of one kernel.
///
/// Ethane's own equality is the row union-find, which deliberately does not
/// see through separately appended but identical rows. That is the right
/// answer for the kernel and the wrong one for asking "did these two
/// constructions build the same thing", which is what this is for.
fn same_shape(kernel: &Kernel, left: Ref, right: Ref) -> bool {
    let table = Table::from_arena(kernel.arena().clone()).expect("table");
    let mut pending = vec![(left, right)];
    let mut seen: BTreeSet<(Ref, Ref)> = BTreeSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((left, right)) {
            continue;
        }
        let (Some(left), Some(right)) = (table.expr(left), table.expr(right)) else {
            return false;
        };
        if left.tag() != right.tag()
            || left.name() != right.name()
            || left.bool_value() != right.bool_value()
            || left.op1() != right.op1()
            || left.op2() != right.op2()
        {
            return false;
        }
        let (left, right): (Vec<_>, Vec<_>) =
            (left.children().collect(), right.children().collect());
        if left.len() != right.len() {
            return false;
        }
        pending.extend(left.into_iter().zip(right));
    }
    true
}

fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Ref {
    let theorem = kernel.thm().get(theorem).expect("theorem");
    assert!(theorem.lhs.rows().next().is_none());
    let rows = theorem.rhs.to_rows();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].len(), 1);
    assert!(rows[0][0].is_positive());
    Ref::new(i32::try_from(rows[0][0].magnitude()).expect("Ref magnitude")).expect("nonzero Ref")
}

#[test]
fn the_package_builds_and_every_piece_lands_in_the_right_category() {
    let mut fix = Fix::identity_on_bool().licensed();
    let built = fix.guarded().expect("subtype");
    let declaration = built.declaration();
    let proof = built.proof();

    assert_eq!(declaration.sub, built.sub);
    assert_eq!(declaration.property, built.property);
    assert_eq!(proof.property, built.property_theorem);
    assert_eq!(
        proof.model,
        built
            .model
            .map(covalence_logic_hol_derived::ChosenModel::proof)
    );

    assert_eq!(fix.kernel.category(built.sub).expect("sub"), Sort::Ty);
    for term in [
        built.rep,
        built.abs,
        built.abs_rep,
        built.rep_abs,
        built.rep_guarded,
    ] {
        assert_eq!(fix.kernel.category(term).expect("term"), Sort::Tm);
    }
    for law in [built.abs_rep, built.rep_abs, built.rep_guarded] {
        let classifier = fix.kernel.classifier(law).expect("classifier");
        assert!(
            fix.kernel
                .equivalent(classifier, fix.bool_ty)
                .expect("equivalent"),
            "every package law must be Boolean"
        );
    }
}

#[test]
fn rep_and_abs_have_the_types_the_laws_need() {
    let mut fix = Fix::identity_on_bool().licensed();
    let built = fix.guarded().expect("subtype");

    // The package must hand back the arrow rows, because a rebuilt arrow is a
    // different type under Ethane's union-find equality.
    assert_eq!(
        fix.kernel.classifier(built.rep).expect("rep type"),
        built.rep_ty
    );
    assert_eq!(
        fix.kernel.classifier(built.abs).expect("abs type"),
        built.abs_ty
    );

    let rebuilt = fix
        .kernel
        .ty_arr(built.sub, built.carrier)
        .expect("sub -> A");
    assert!(
        !fix.kernel
            .equivalent(built.rep_ty, rebuilt)
            .expect("equivalent"),
        "structural identity is not type equality here; the exposed row is the usable one"
    );

    // `rep` and `abs` compose, which is what the laws quantify over.
    let value = fix
        .kernel
        .tm_fv(built.base_name + 100, built.carrier)
        .expect("value");
    let abstracted = fix.kernel.app(built.abs, value).expect("abs a");
    let restored = fix.kernel.app(built.rep, abstracted).expect("rep (abs a)");
    assert_eq!(
        fix.kernel.classifier(restored).expect("restored type"),
        built.carrier
    );
}

#[test]
fn each_chosen_package_law_is_an_exact_premise_free_theorem() {
    let mut fix = Fix::identity_on_bool().licensed();
    let built = fix.guarded().expect("subtype");

    assert_eq!(
        sole_conclusion(
            &fix.kernel,
            built.property_theorem.expect("property theorem")
        ),
        built.property
    );
    assert_eq!(
        sole_conclusion(&fix.kernel, built.abs_rep_theorem.expect("abs-rep theorem")),
        built.abs_rep
    );
    assert_eq!(
        sole_conclusion(&fix.kernel, built.rep_abs_theorem.expect("rep-abs theorem")),
        built.rep_abs
    );
    assert_eq!(
        sole_conclusion(
            &fix.kernel,
            built.rep_guarded_theorem.expect("guarded theorem")
        ),
        built.rep_guarded
    );

    let model = built.model.expect("model");
    assert_eq!(
        sole_conclusion(&fix.kernel, model.theorem),
        model.specification
    );
    assert_eq!(
        fix.kernel
            .thm()
            .get(built.property_theorem.expect("property theorem"))
            .expect("property theorem")
            .rhs
            .to_rows()[0]
            .as_slice(),
        [Lit::positive(built.property.get())]
    );
}

#[test]
fn the_subtype_is_the_one_the_axiom_is_about() {
    // The whole point of taking `package` and `model_name` from the axiom: the
    // subtype has to be the model the concluded sentence quantifies, not a
    // parallel construction that happens to look similar.
    let mut fix = Fix::identity_on_bool().licensed();
    let built = fix.guarded().expect("subtype");
    let axiom = built.axiom.expect("built through the axiom");
    let model = built.model.expect("opened chosen model");

    let expected = fix
        .kernel
        .model(axiom.model_name, axiom.package_body)
        .expect("model");
    assert!(
        same_shape(&fix.kernel, built.sub, expected),
        "the subtype must be `model` of the sentence's own body"
    );
    assert_eq!(
        built.sub, model.ty,
        "the usable subtype is the proved choice"
    );
    assert_eq!(built.theorem(), Some(model.theorem));
    assert_eq!(built.existence_theorem(), Some(axiom.theorem));
    assert_eq!(built.base_name, axiom.base_name);
}

#[test]
fn the_untrusted_rebuild_still_agrees_with_the_kernel() {
    // This module rebuilds the package body rather than borrowing the kernel's,
    // so that it stays replaceable. Drift would be silent — the laws would
    // quietly stop being about the concluded sentence — so it is checked.
    let mut fix = Fix::identity_on_bool().licensed();
    let axiom = fix
        .kernel
        .sub_exists(fix.bool_ty, fix.carrier, fix.predicate)
        .expect("axiom");
    let rebuilt = fix
        .kernel
        .subtype_terms(fix.bool_ty, fix.carrier, fix.predicate)
        .expect("terms");
    let expected = fix
        .kernel
        .model(axiom.model_name, axiom.package_body)
        .expect("model");

    assert!(
        same_shape(&fix.kernel, rebuilt.sub, expected),
        "the untrusted package body has drifted from the kernel's"
    );
}

#[test]
fn same_shape_is_not_vacuous() {
    let mut fix = Fix::identity_on_bool();
    let truth = fix.kernel.bool(fix.bool_ty, true).expect("true");
    let falsehood = fix.kernel.bool(fix.bool_ty, false).expect("false");
    let other = fix.kernel.bool(fix.bool_ty, true).expect("true again");
    assert!(
        same_shape(&fix.kernel, truth, other),
        "same literal, two rows"
    );
    assert!(
        !same_shape(&fix.kernel, truth, falsehood),
        "different literals"
    );
}

#[test]
fn building_terms_alone_takes_on_no_axiom() {
    let mut fix = Fix::identity_on_bool();
    let built = fix
        .kernel
        .subtype_terms(fix.bool_ty, fix.carrier, fix.predicate)
        .expect("terms");
    assert!(built.axiom.is_none());
    assert!(built.theorem().is_none());
    assert_eq!(
        fix.kernel.arena().axioms().count(),
        0,
        "constructing a subtype's syntax must not commit the arena to anything"
    );
}

#[test]
fn the_full_package_requires_the_capability() {
    let mut fix = Fix::identity_on_bool();
    assert!(matches!(
        fix.guarded(),
        Err(SubtypeError::Kernel {
            source: KernelError::MissingAxiom { name: AX_SUB }
        })
    ));
}

#[test]
fn the_binder_names_are_the_ones_the_axiom_reserved() {
    let mut fix = Fix::identity_on_bool().licensed();
    let built = fix.guarded().expect("subtype");
    assert_eq!(built.name_of(Binder::ModelType), built.base_name);
    assert_eq!(built.name_of(Binder::Conjunction), built.base_name + 6);
}
