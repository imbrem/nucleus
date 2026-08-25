//! The guarded subtype package and the `ax.sub` capability that licenses it.

mod support;

use covalence_logic_hol::{AX_SUB, Binder, Kernel, KernelError, Lit, Ref, Sort};
use support::Fix;

/// A kernel with `star`, `bool`, a carrier, and a predicate over it.
struct Package {
    fix: Fix,
    carrier: Ref,
    predicate: Ref,
}

impl Package {
    /// Carrier `bool`, predicate `λx. x` — the smallest package that is not
    /// degenerate, and one whose guard is satisfiable.
    fn identity_on_bool() -> Self {
        let mut fix = Fix::new();
        let carrier = fix.bool_ty;
        let variable = fix.tm_fv(0, carrier).expect("binder");
        let predicate = fix.lam(variable, variable).expect("predicate");
        Self {
            fix,
            carrier,
            predicate,
        }
    }

    fn build(&mut self) -> Result<covalence_logic_hol::Subtype, KernelError> {
        let bool_ty = self.fix.bool_ty;
        self.fix
            .kernel
            .subtype(bool_ty, self.carrier, self.predicate)
    }
}

#[test]
fn the_package_builds_and_every_piece_lands_in_the_right_category() {
    let mut package = Package::identity_on_bool();
    let built = package.build().expect("package");
    let kernel = &package.fix.kernel;

    assert_eq!(kernel.category(built.sub).expect("sub"), Sort::Ty);
    for term in [
        built.exists_type,
        built.rep,
        built.abs,
        built.abs_rep,
        built.rep_abs,
        built.rep_guarded,
    ] {
        assert_eq!(kernel.category(term).expect("term"), Sort::Tm);
    }
    // The sentence and the three laws are propositions.
    for proposition in [
        built.exists_type,
        built.abs_rep,
        built.rep_abs,
        built.rep_guarded,
    ] {
        let classifier = kernel.classifier(proposition).expect("classifier");
        assert!(
            kernel
                .equivalent(classifier, package.fix.bool_ty)
                .expect("equivalent"),
            "every package law must be Boolean"
        );
    }
}

#[test]
fn rep_and_abs_have_the_types_the_laws_need() {
    let mut package = Package::identity_on_bool();
    let built = package.build().expect("package");
    let kernel = &mut package.fix.kernel;

    // The package must hand back the arrow rows, because a rebuilt arrow is a
    // different type under Ethane's union-find equality.
    assert_eq!(
        kernel.classifier(built.rep).expect("rep type"),
        built.rep_ty
    );
    assert_eq!(
        kernel.classifier(built.abs).expect("abs type"),
        built.abs_ty
    );

    let rebuilt = kernel.ty_arr(built.sub, built.carrier).expect("sub -> A");
    assert!(
        !kernel
            .equivalent(built.rep_ty, rebuilt)
            .expect("equivalent"),
        "structural identity is not type equality here; the exposed row is the usable one"
    );

    // `rep` and `abs` compose, which is what the laws quantify over.
    let value = kernel
        .tm_fv(built.base_name + 100, built.carrier)
        .expect("value");
    let abstracted = kernel.app(built.abs, value).expect("abs a");
    let restored = kernel.app(built.rep, abstracted).expect("rep (abs a)");
    assert_eq!(
        kernel.classifier(restored).expect("restored type"),
        built.carrier
    );
}

#[test]
fn the_private_binders_sit_above_every_name_the_caller_used() {
    let mut fix = Fix::new();
    let carrier = fix.bool_ty;
    // A caller name far from zero: the package must clear it, not assume a
    // dense name space.
    let variable = fix.tm_fv(41, carrier).expect("binder");
    let predicate = fix.lam(variable, variable).expect("predicate");
    let bool_ty = fix.bool_ty;
    let built = fix
        .kernel
        .subtype(bool_ty, carrier, predicate)
        .expect("package");

    assert_eq!(built.base_name, 42);
    assert_eq!(built.name_of(Binder::ModelType), 42);
    assert_eq!(built.name_of(Binder::Conjunction), 48);
}

#[test]
fn the_package_depends_on_its_arguments_and_not_on_the_surrounding_arena() {
    // Content addressing needs the same carrier and predicate to yield the
    // same sentence wherever they appear, so unrelated rows must not shift the
    // private names.
    let mut bare = Package::identity_on_bool();
    let bare_built = bare.build().expect("package");

    let mut cluttered = Package::identity_on_bool();
    for name in 0..5 {
        cluttered
            .fix
            .tm_fv(100 + name, cluttered.carrier)
            .expect("unrelated row");
    }
    let cluttered_built = cluttered.build().expect("package");

    assert_eq!(
        bare_built.base_name, cluttered_built.base_name,
        "unrelated rows must not perturb the package's binder names"
    );
}

#[test]
fn a_predicate_of_the_wrong_type_is_refused() {
    let mut fix = Fix::new();
    let carrier = fix.bool_ty;
    let bool_ty = fix.bool_ty;
    // A Boolean term, not a Boolean *predicate*.
    let truth = fix.lit(true);
    assert!(matches!(
        fix.kernel.subtype(bool_ty, carrier, truth),
        Err(KernelError::WrongForm { .. } | KernelError::ClassifierMismatch { .. })
    ));
}

#[test]
fn concluding_the_sentence_requires_the_capability() {
    let mut package = Package::identity_on_bool();
    let bool_ty = package.fix.bool_ty;
    let carrier = package.carrier;
    let predicate = package.predicate;

    assert!(
        matches!(
            package.fix.kernel.sub_exists(bool_ty, carrier, predicate),
            Err(KernelError::MissingAxiom { name: AX_SUB })
        ),
        "an arena that has not declared ax.sub must not be able to use it"
    );

    package.fix.kernel.add_axiom(AX_SUB).expect("capability");
    let (built, theorem) = package
        .fix
        .kernel
        .sub_exists(bool_ty, carrier, predicate)
        .expect("axiom");

    let sequent = package.fix.kernel.thm().get(theorem).expect("sequent");
    assert!(
        sequent.lhs.to_rows().is_empty(),
        "the axiom is premise-free"
    );
    let conclusions = sequent.rhs.to_rows();
    assert_eq!(conclusions.len(), 1, "one cube");
    assert_eq!(
        conclusions[0].as_slice(),
        [Lit::positive(built.exists_type.get())],
        "the conclusion must be the sentence the kernel itself built"
    );
}

#[test]
fn the_capability_is_recorded_in_the_arena() {
    let mut kernel = Kernel::new();
    kernel.add_axiom(AX_SUB).expect("capability");
    let arena = kernel.arena();
    assert!(
        arena.axioms().any(|name| name == AX_SUB),
        "an auditor reading the arena must see which axioms it used"
    );
}

#[test]
fn an_unknown_capability_is_still_refused() {
    let mut kernel = Kernel::new();
    assert!(matches!(
        kernel.add_axiom("ax.choice"),
        Err(KernelError::UnsupportedAxiom { .. })
    ));
}

#[test]
fn the_package_is_a_few_hundred_rows_not_a_few_thousand() {
    // The three laws appear four times over: once under the `ty.exists`
    // binder, once each while choosing `rep` and `abs`, and once against the
    // chosen pair. Ethane does not hash-cons, so that repetition is real rows
    // and worth a number rather than a shrug: 465 for the smallest package.
    // The band is wide because the figure is a fact to notice changing, not a
    // budget to defend.
    let mut package = Package::identity_on_bool();
    let before = package.fix.kernel.len();
    package.build().expect("package");
    let appended = package.fix.kernel.len() - before;
    assert!(
        (100..1000).contains(&appended),
        "the package appended {appended} rows, which is outside the expected band"
    );
}

#[test]
fn a_carrier_and_predicate_with_no_names_still_start_at_one() {
    // The empty case is where an off-by-one hides. `freshBase` on the Lean side
    // is `Finset.sup ∅ + 1 = 1`, and the two constructions have to agree here
    // as much as anywhere else.
    let mut fix = Fix::new();
    let carrier = fix.bool_ty;
    let bool_ty = fix.bool_ty;
    // `λ_. true` over a binder named 0 is the smallest predicate that mentions
    // a name; drop to a predicate mentioning none by using `eps`.
    let truth = fix.lit(true);
    let anonymous = fix.tm_fv(0, carrier).expect("binder");
    let predicate = fix.lam(anonymous, truth).expect("predicate");
    let built = fix
        .kernel
        .subtype(bool_ty, carrier, predicate)
        .expect("package");
    assert_eq!(
        built.base_name, 1,
        "the largest name is 0, so the package starts at 1"
    );
}
