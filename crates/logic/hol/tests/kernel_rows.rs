//! Row construction, classifier bookkeeping, and the row union-find that the
//! syntactic-fact cache feeds.

mod support;

use covalence_logic_hol::{KernelError, KindTag, Ref, Sort, SynRel, Tag, TmTag, TyTag};
use support::{Fix, row_id};

#[test]
fn each_constructor_records_its_own_tag_and_classifier() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let arrow = fix.bool_arrow();
    let variable = fix.var(0);
    let truth = fix.lit(true);
    let identity = fix.lam(variable, variable).expect("identity");
    let applied = fix.app(identity, truth).expect("application");
    let equation = fix.eq(bool_ty, applied, truth).expect("equality");
    let predicate = fix.tm_fv(1, arrow).expect("predicate");
    let choice = fix.eps(bool_ty, predicate).expect("choice");
    let model = fix.model(2, truth).expect("model");
    let existential = fix.ty_exists(3, truth).expect("existential");
    let universal = fix.ty_forall(5, truth).expect("universal");

    for (row, tag, classifier) in [
        (star, Tag::Kind(KindTag::Star), None),
        (bool_ty, Tag::Ty(TyTag::Bool), Some(star)),
        (arrow, Tag::Ty(TyTag::Arr), Some(star)),
        (variable, Tag::Tm(TmTag::Fv), Some(bool_ty)),
        (truth, Tag::Tm(TmTag::Bool), Some(bool_ty)),
        (applied, Tag::Tm(TmTag::App), Some(bool_ty)),
        (equation, Tag::Tm(TmTag::Eq), Some(bool_ty)),
        (choice, Tag::Tm(TmTag::Eps), Some(bool_ty)),
        (model, Tag::Ty(TyTag::Model), Some(star)),
        (existential, Tag::Tm(TmTag::TyExists), Some(bool_ty)),
        (universal, Tag::Tm(TmTag::TyForall), Some(bool_ty)),
    ] {
        assert_eq!(fix.arena().tag(row), Some(tag), "{row:?}");
        assert_eq!(fix.classifier(row).ok(), classifier, "{row:?}");
    }
    assert_eq!(fix.category(star).expect("resident"), Sort::Kind);
    assert_eq!(fix.category(bool_ty).expect("resident"), Sort::Ty);
    assert_eq!(fix.category(truth).expect("resident"), Sort::Tm);
}

#[test]
fn higher_kinded_rows_carry_a_synthesized_arrow_kind() {
    let mut fix = Fix::new();
    let star = fix.star;
    let arrow_kind = fix.kind_arr(star, star).expect("arrow kind");
    let family = fix.ty_fv(0, arrow_kind).expect("family variable");
    let argument = fix.ty_fv(1, star).expect("type variable");
    let applied = fix.ty_app(family, argument).expect("family application");
    let abstraction = fix.ty_lam(argument, applied).expect("family abstraction");

    assert_eq!(fix.classifier(applied).expect("kinded"), star);
    let kind = fix.classifier(abstraction).expect("kinded");
    assert_eq!(fix.arena().tag(kind), Some(Tag::Kind(KindTag::Arr)));
    assert_eq!(
        fix.arena()
            .children(kind)
            .expect("resident")
            .collect::<Vec<_>>(),
        [star, star]
    );
}

#[test]
fn a_missing_row_is_a_missing_row_wherever_it_is_named() {
    let mut fix = Fix::new();
    let absent = row_id(64);
    let star = fix.star;

    assert!(matches!(
        fix.category(absent),
        Err(KernelError::MissingDefinition { reference }) if reference == absent
    ));
    assert!(fix.classifier(absent).is_err());
    assert!(fix.find(absent).is_err());
    assert!(fix.kind_arr(absent, star).is_err());
    assert!(fix.bool_ty(absent).is_err());
    assert!(fix.tm_fv(0, absent).is_err());
    assert!(fix.arena().tag(absent).is_none());
    assert!(fix.arena().children(absent).is_none());
}

#[test]
fn a_kind_row_has_no_classifier() {
    let mut fix = Fix::new();
    let star = fix.star;
    let arrow_kind = fix.kind_arr(star, star).expect("arrow kind");
    for kind in [star, arrow_kind] {
        assert!(matches!(
            fix.classifier(kind),
            Err(KernelError::MissingSort { .. })
        ));
    }
}

#[test]
fn constructors_check_the_syntactic_category_of_every_operand() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let truth = fix.lit(true);

    let wrong: [Result<Ref, KernelError>; 6] = [
        fix.kind_arr(bool_ty, star),
        fix.ty_arr(star, bool_ty),
        fix.ty_app(bool_ty, truth),
        fix.tm_fv(0, star),
        fix.app(truth, truth),
        fix.eq(bool_ty, bool_ty, truth),
    ];
    for result in wrong {
        assert!(
            matches!(
                result,
                Err(KernelError::WrongCategory { .. } | KernelError::WrongForm { .. })
            ),
            "expected a category or form rejection, got {result:?}"
        );
    }
}

#[test]
fn the_boolean_type_must_literally_have_kind_star() {
    let mut fix = Fix::new();
    let star = fix.star;
    let arrow_kind = fix.kind_arr(star, star).expect("arrow kind");
    let family = fix.ty_fv(0, arrow_kind).expect("family variable");

    assert!(matches!(
        fix.bool_ty(arrow_kind),
        Err(KernelError::WrongForm {
            expected: "kind.star",
            ..
        })
    ));
    // A higher-kinded family is a type, but not one terms can inhabit.
    assert!(matches!(
        fix.tm_fv(0, family),
        Err(KernelError::WrongForm {
            expected: "kind.star",
            ..
        })
    ));
}

#[test]
fn family_application_compares_kinds_syntactically_not_up_to_equality() {
    let mut fix = Fix::new();
    let star = fix.star;
    let other_star = fix.star().expect("second star");
    let arrow_kind = fix.kind_arr(star, star).expect("arrow kind");
    let family = fix.ty_fv(0, arrow_kind).expect("family variable");
    let argument = fix.ty_fv(1, other_star).expect("argument at the twin kind");

    // Kinds are syntactic in Ethane, so the twin `kind.star` row is not the
    // arrow's domain even though nothing distinguishes the two rows.
    assert!(matches!(
        fix.ty_app(family, argument),
        Err(KernelError::ClassifierMismatch { .. })
    ));
    let matching = fix.ty_fv(2, star).expect("argument at the exact kind");
    assert!(fix.ty_app(family, matching).is_ok());
}

#[test]
fn term_application_finds_an_arrow_anywhere_in_the_function_type_class() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let arrow = fix.bool_arrow();
    // `(λα. α) (bool -> bool)` is a type that is not syntactically an arrow.
    let binder = fix.ty_fv(0, star).expect("type variable");
    let family = fix.ty_lam(binder, binder).expect("identity family");
    let redex = fix.ty_app(family, arrow).expect("family application");
    let function = fix.tm_fv(1, redex).expect("function at the redex type");
    let truth = fix.lit(true);

    assert!(
        matches!(fix.app(function, truth), Err(KernelError::WrongForm { .. })),
        "nothing yet says the redex reduces to an arrow"
    );

    let substitution = fix.syn_sub_var(None, binder, arrow).expect("sub var");
    let beta = fix
        .ty_beta_fact(None, redex, substitution)
        .expect("family beta");
    fix.union_syn_fact(beta).expect("record the equality");

    assert!(fix.ty_eq(redex, arrow).expect("resident"));
    let applied = fix
        .app(function, truth)
        .expect("the class now contains an arrow");
    assert_eq!(fix.classifier(applied).expect("typed"), bool_ty);
}

#[test]
fn the_boolean_type_may_be_any_member_of_a_class_containing_ty_bool() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let alias = fix.bool_ty(star).expect("second bool type");

    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, bool_ty, alias)
        .expect("merge the duplicate type rows");
    assert!(
        fix.bool(alias, true).is_ok(),
        "a class containing `ty.bool` is Boolean"
    );

    let opaque = fix.ty_fv(0, star).expect("type variable");
    assert!(matches!(
        fix.bool(opaque, true),
        Err(KernelError::WrongForm { .. })
    ));
}

#[test]
fn equality_requires_the_two_sides_to_share_a_type_class() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let alias = fix.bool_ty(star).expect("second bool type");
    let left = fix.lit(true);
    let right = fix.bool(alias, false).expect("literal at the twin type");

    assert!(matches!(
        fix.eq(bool_ty, left, right),
        Err(KernelError::ClassifierMismatch { .. })
    ));

    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, bool_ty, alias)
        .expect("merge the duplicate type rows");
    assert!(fix.eq(bool_ty, left, right).is_ok());
}

#[test]
fn equality_can_retain_an_exact_equivalent_operand_type() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let alias = fix.bool_ty(star).expect("second bool type");
    let left = fix.lit(true);
    let right = fix.bool(alias, false).expect("literal at the twin type");
    fix.prover()
        .union_equal(&mut fix.kernel, bool_ty, alias)
        .expect("merge the duplicate type rows");

    let equality = fix
        .eq_at(bool_ty, alias, left, right)
        .expect("targeted equality");
    assert_eq!(
        fix.arena()
            .children(equality)
            .expect("equality children")
            .collect::<Vec<_>>(),
        [alias, left, right]
    );

    let unrelated = fix.ty_fv(7, star).expect("unrelated type");
    assert!(matches!(
        fix.eq_at(bool_ty, unrelated, left, right),
        Err(KernelError::ClassifierMismatch { .. })
    ));
}

#[test]
fn choice_requires_a_predicate_over_exactly_the_chosen_type() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let arrow = fix.bool_arrow();
    let predicate = fix.tm_fv(0, arrow).expect("predicate");
    assert!(fix.eps(bool_ty, predicate).is_ok());

    // A predicate over another type is not a predicate over this one.
    let other = fix.ty_fv(1, star).expect("type variable");
    let other_arrow = fix.ty_arr(other, bool_ty).expect("other -> bool");
    let mismatched = fix.tm_fv(2, other_arrow).expect("predicate");
    assert!(matches!(
        fix.eps(bool_ty, mismatched),
        Err(KernelError::ClassifierMismatch { .. })
    ));

    // Nor is a function that does not land in `bool`.
    let endo = fix.ty_arr(bool_ty, other).expect("bool -> other");
    let not_a_predicate = fix.tm_fv(3, endo).expect("function");
    assert!(matches!(
        fix.eps(bool_ty, not_a_predicate),
        Err(KernelError::WrongForm { .. })
    ));
}

#[test]
fn the_logical_context_and_axiom_set_are_both_checked() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let proposition = fix.lit(true);
    fix.add_context(proposition).expect("Boolean proposition");
    // The context is a set, so re-adding is idempotent.
    fix.add_context(proposition).expect("Boolean proposition");
    assert_eq!(fix.arena().context().collect::<Vec<_>>(), [proposition]);

    assert!(matches!(
        fix.add_context(bool_ty),
        Err(KernelError::WrongCategory { .. })
    ));

    fix.add_axiom("ax.inf").expect("the one supported axiom");
    fix.add_axiom("ax.inf").expect("idempotent");
    assert_eq!(fix.arena().axioms().collect::<Vec<_>>(), ["ax.inf"]);
    for name in ["ax.choice", "", "AX.INF", "ax.inf "] {
        assert!(matches!(
            fix.add_axiom(name),
            Err(KernelError::UnsupportedAxiom { .. })
        ));
    }
}

#[test]
fn merging_classes_keeps_the_smallest_row_canonical() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let star = fix.star;
    let copies: Vec<Ref> = (0..5)
        .map(|_| fix.bool_ty(star).expect("duplicate bool type"))
        .collect();
    let prover = fix.prover();

    // Merge the copies in descending order; the smallest row must still win.
    for window in copies.windows(2).rev() {
        prover
            .union_equal(&mut fix.kernel, window[1], window[0])
            .expect("duplicates merge");
    }
    prover
        .union_equal(&mut fix.kernel, copies[0], bool_ty)
        .expect("duplicates merge");

    for copy in &copies {
        assert_eq!(fix.find(*copy).expect("resident"), bool_ty);
        assert!(fix.ty_eq(*copy, bool_ty).expect("resident"));
    }
}

#[test]
fn path_compression_preserves_the_partition() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let copies: Vec<Ref> = (0..4)
        .map(|_| fix.bool_ty(star).expect("duplicate bool type"))
        .collect();
    let prover = fix.prover();
    for window in copies.windows(2) {
        prover
            .union_equal(&mut fix.kernel, window[0], window[1])
            .expect("duplicates merge");
    }

    let mut rows = copies.clone();
    rows.push(bool_ty);
    let before: Vec<bool> = rows
        .iter()
        .flat_map(|left| {
            rows.iter()
                .map(|right| fix.equivalent(*left, *right).expect("resident"))
                .collect::<Vec<_>>()
        })
        .collect();

    for row in &rows {
        let root = fix.find(*row).expect("resident");
        assert_eq!(fix.find_mut(*row).expect("resident"), root);
        // Compression is idempotent and does not move the root.
        assert_eq!(fix.find_mut(*row).expect("resident"), root);
    }

    let after: Vec<bool> = rows
        .iter()
        .flat_map(|left| {
            rows.iter()
                .map(|right| fix.equivalent(*left, *right).expect("resident"))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(before, after, "compression changed the equality relation");
}

#[test]
fn rows_in_different_categories_are_never_equivalent() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let truth = fix.lit(true);

    for (left, right) in [(star, bool_ty), (bool_ty, truth), (star, truth)] {
        assert!(
            !fix.equivalent(left, right).expect("resident"),
            "{left:?} and {right:?} span two categories"
        );
        assert!(!fix.equivalent_mut(left, right).expect("resident"));
    }
    // The typed wrappers reject rather than answer.
    assert!(fix.ty_eq(star, bool_ty).is_err());
    assert!(fix.tm_eq(bool_ty, truth).is_err());
}

#[test]
fn the_kernel_hands_back_exactly_the_arena_it_built() {
    let mut fix = Fix::new();
    let truth = fix.lit(true);
    fix.add_context(truth).expect("Boolean proposition");
    fix.syn_refl(None, SynRel::Conv, truth)
        .expect("reflexivity");

    let borrowed = fix.arena().clone();
    let owned = fix.kernel.into_arena();
    assert_eq!(borrowed, owned);
    support::assert_round_trips(&owned);
}

#[test]
fn type_quantifiers_are_boolean_propositions_over_a_bound_type_variable() {
    // The universal is the dual of the existential and shares its shape: a
    // Boolean term with a type variable free, quantified into a proposition.
    // What differs is only what it asserts, which is invisible to the row.
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let truth = fix.lit(true);

    let universal = fix.ty_forall(11, truth).expect("universal");
    assert_eq!(fix.category(universal).expect("resident"), Sort::Tm);
    assert_eq!(fix.classifier(universal).ok(), Some(bool_ty));
    assert_eq!(fix.arena().name(universal), Some(11));

    // A non-Boolean body is refused, as for the existential.
    assert!(fix.ty_forall(12, bool_ty).is_err());

    // Two quantifiers over the same body are distinct rows and distinct
    // propositions: Ethane does not hash-cons, and in any case "some type
    // satisfies P" is not "every type satisfies P".
    let existential = fix.ty_exists(11, truth).expect("existential");
    assert_ne!(universal, existential);
    assert_ne!(fix.arena().tag(universal), fix.arena().tag(existential));
}

#[test]
fn a_type_universal_reserves_its_binder_name() {
    let mut fix = Fix::new();
    let truth = fix.lit(true);
    let universal = fix.ty_forall(41, truth).expect("universal");

    assert_eq!(fix.fresh_name(&[universal]).expect("fresh name"), 42);
}
