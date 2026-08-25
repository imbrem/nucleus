//! The subtype-package axiom: the sentence it concludes, and the capability
//! that licenses it.
//!
//! The usable package built on top — `sub`, `rep`, `abs`, the laws — is not
//! here, because it is not in the kernel. See `covalence-nucleus`'s
//! `SubtypeExt` and its tests.

mod support;

use covalence_logic_hol::{AX_SUB, Binder, Kernel, KernelError, Lit, Ref, Sort, SubtypeAxiom};
use support::Fix;

/// A kernel with `star`, `bool`, a carrier, and a predicate over it.
struct Package {
    fix: Fix,
    carrier: Ref,
    predicate: Ref,
}

impl Package {
    /// Carrier `bool`, predicate `λx. x`.
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

    fn licensed(mut self) -> Self {
        self.fix.kernel.add_axiom(AX_SUB).expect("capability");
        self
    }

    fn conclude(&mut self) -> Result<SubtypeAxiom, KernelError> {
        let bool_ty = self.fix.bool_ty;
        self.fix
            .kernel
            .sub_exists(bool_ty, self.carrier, self.predicate)
    }
}

#[test]
fn the_sentence_is_a_proposition_and_the_body_is_what_quantifies_it() {
    let mut package = Package::identity_on_bool().licensed();
    let axiom = package.conclude().expect("axiom");
    let kernel = &package.fix.kernel;

    assert_eq!(
        kernel.category(axiom.exists_type).expect("sentence"),
        Sort::Tm
    );
    let classifier = kernel.classifier(axiom.exists_type).expect("classifier");
    assert!(
        kernel
            .equivalent(classifier, package.fix.bool_ty)
            .expect("equivalent"),
        "the package sentence is Boolean"
    );
    assert_eq!(kernel.category(axiom.package).expect("body"), Sort::Tm);
}

#[test]
fn the_body_and_the_model_name_are_enough_to_name_the_subtype() {
    // This is the whole contract with the untrusted layer: given these, it can
    // build the subtype the sentence is about rather than a parallel one.
    let mut package = Package::identity_on_bool().licensed();
    let axiom = package.conclude().expect("axiom");
    let sub = package
        .fix
        .kernel
        .model(axiom.model_name, axiom.package)
        .expect("subtype");
    assert_eq!(package.fix.kernel.category(sub).expect("sub"), Sort::Ty);
    assert_eq!(axiom.model_name, axiom.name_of(Binder::ModelType));
}

#[test]
fn concluding_requires_the_capability() {
    let mut package = Package::identity_on_bool();
    assert!(
        matches!(
            package.conclude(),
            Err(KernelError::MissingAxiom { name: AX_SUB })
        ),
        "an arena that has not declared ax.sub must not be able to use it"
    );
}

#[test]
fn the_conclusion_is_the_sentence_the_kernel_itself_built() {
    let mut package = Package::identity_on_bool().licensed();
    let axiom = package.conclude().expect("axiom");
    let sequent = package
        .fix
        .kernel
        .thm()
        .get(axiom.theorem)
        .expect("sequent");

    assert!(
        sequent.lhs.to_rows().is_empty(),
        "the axiom is premise-free"
    );
    let conclusions = sequent.rhs.to_rows();
    assert_eq!(conclusions.len(), 1, "one cube");
    assert_eq!(
        conclusions[0].as_slice(),
        [Lit::positive(axiom.exists_type.get())]
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
    fix.kernel.add_axiom(AX_SUB).expect("capability");
    let axiom = fix
        .kernel
        .sub_exists(bool_ty, carrier, predicate)
        .expect("axiom");

    assert_eq!(axiom.base_name, 42);
    assert_eq!(axiom.name_of(Binder::ModelType), 42);
    assert_eq!(axiom.name_of(Binder::Conjunction), 48);
}

#[test]
fn a_carrier_and_predicate_with_no_names_still_start_at_one() {
    // `Nucleus.Hol.Ethane.Subtype.freshBase` is `Finset.sup ∅ + 1 = 1`, and the
    // two constructions have to agree here as much as anywhere else.
    let mut fix = Fix::new();
    let carrier = fix.bool_ty;
    let truth = fix.lit(true);
    let anonymous = fix.tm_fv(0, carrier).expect("binder");
    let predicate = fix.lam(anonymous, truth).expect("predicate");
    assert_eq!(
        fix.kernel.fresh_name(&[carrier, predicate]).expect("base"),
        1,
        "the largest name is 0, so the package starts at 1"
    );
}

#[test]
fn the_base_depends_on_its_arguments_and_not_on_the_surrounding_arena() {
    // Content addressing needs the same carrier and predicate to yield the
    // same sentence wherever they appear, so unrelated rows must not shift the
    // private names.
    let bare = Package::identity_on_bool();
    let bare_base = bare
        .fix
        .kernel
        .fresh_name(&[bare.carrier, bare.predicate])
        .expect("base");

    let mut cluttered = Package::identity_on_bool();
    for name in 0..5 {
        cluttered
            .fix
            .tm_fv(100 + name, cluttered.carrier)
            .expect("unrelated row");
    }
    let cluttered_base = cluttered
        .fix
        .kernel
        .fresh_name(&[cluttered.carrier, cluttered.predicate])
        .expect("base");

    assert_eq!(
        bare_base, cluttered_base,
        "unrelated rows must not perturb the package's binder names"
    );
}

#[test]
fn a_predicate_of_the_wrong_type_is_refused() {
    let mut fix = Fix::new();
    let carrier = fix.bool_ty;
    let bool_ty = fix.bool_ty;
    fix.kernel.add_axiom(AX_SUB).expect("capability");
    // A Boolean term, not a Boolean *predicate*.
    let truth = fix.lit(true);
    assert!(matches!(
        fix.kernel.sub_exists(bool_ty, carrier, truth),
        Err(KernelError::WrongForm { .. } | KernelError::ClassifierMismatch { .. })
    ));
}

#[test]
fn the_capability_is_recorded_in_the_arena() {
    let mut kernel = Kernel::new();
    kernel.add_axiom(AX_SUB).expect("capability");
    assert!(
        kernel.arena().axioms().any(|name| name == AX_SUB),
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
