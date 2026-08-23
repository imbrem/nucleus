//! Binder congruence, alpha renaming, beta, eta, and the `Model` conversion
//! barrier, plus the invariants every minted fact has to satisfy.

mod support;

use covalence_logic_hol::{KernelError, Ref, SynFactId, SynRel};
use support::{Fix, assert_cache_invariants};

fn invalid(error: &KernelError) -> &'static str {
    match error {
        KernelError::InvalidSynFact { rule } => rule,
        other => panic!("expected a rejected local rule, got {other:?}"),
    }
}

/// Merges two structurally identical rows so that endpoint compatibility
/// checks can see them as one class.
fn merge(fix: &mut Fix, left: Ref, right: Ref) {
    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, left, right)
        .expect("structurally identical rows merge");
}

/// `λ name. body` together with its freshly minted function type merged into
/// `arrow`'s class.
fn lam_at(fix: &mut Fix, binder: Ref, body: Ref, arrow: Ref) -> Ref {
    let lam = fix.lam(binder, body).expect("abstraction");
    let minted = fix.classifier(lam).expect("function type");
    if minted != arrow {
        merge(fix, minted, arrow);
    }
    lam
}

#[test]
fn binder_congruence_rewrites_a_body_without_touching_the_binder() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let binder = fix.var(0);
    let free = fix.var(1);
    let value = fix.lit(true);
    let input = lam_at(&mut fix, binder, free, arrow);
    let output = lam_at(&mut fix, binder, value, arrow);

    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, binder)
        .expect("reflexivity");
    let body_fact = fix.syn_sub_var(None, free, value).expect("sub var");
    let id = fix
        .syn_binder_congr(
            None,
            SynRel::Syn,
            Some(free),
            Some(value),
            input,
            output,
            binder_fact,
            body_fact,
        )
        .expect("binder congruence");

    assert_eq!(fix.syn_fact(id).expect("minted").var(), Some(free));
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn a_binder_shadows_the_substitution_it_binds() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let binder = fix.var(0);
    let value = fix.lit(true);
    let lam = lam_at(&mut fix, binder, binder, arrow);

    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, binder)
        .expect("reflexivity");
    let id = fix
        .syn_binder_congr(
            None,
            SynRel::Syn,
            Some(binder),
            Some(value),
            lam,
            lam,
            binder_fact,
            binder_fact,
        )
        .expect("shadowed substitution");

    let fact = fix.syn_fact(id).expect("minted");
    assert_eq!(fact.input(), lam);
    assert_eq!(fact.output(), lam);
}

#[test]
fn a_binder_refuses_to_capture_the_replacement() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let binder = fix.var(1);
    let free = fix.var(2);
    // The replacement mentions the very name the binder binds.
    let captured = fix.var(1);
    let lam = lam_at(&mut fix, binder, free, arrow);

    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, binder)
        .expect("reflexivity");
    let body_fact = fix.syn_sub_var(None, free, captured).expect("sub var");
    let error = fix
        .syn_binder_congr(
            None,
            SynRel::Syn,
            Some(free),
            Some(captured),
            lam,
            lam,
            binder_fact,
            body_fact,
        )
        .expect_err("capture");
    assert_eq!(invalid(&error), "binder freshness");
}

#[test]
fn two_rows_for_one_binder_name_are_ambiguous_rather_than_equal() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let other_bool = fix.bool_ty(star).expect("second bool type");
    let binder = fix.tm_fv(1, bool_ty).expect("binder");
    let twin = fix
        .tm_fv(1, other_bool)
        .expect("same name, other classifier");
    let value = fix.lit(true);
    let arrow = fix.bool_arrow();
    let lam = lam_at(&mut fix, binder, binder, arrow);
    // Merge the duplicate `ty.bool` rows so the substitution pair itself is
    // well formed and the rule reaches its binder-identity check.
    merge(&mut fix, bool_ty, other_bool);

    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, binder)
        .expect("reflexivity");
    let error = fix
        .syn_binder_congr(
            None,
            SynRel::Syn,
            Some(twin),
            Some(value),
            lam,
            lam,
            binder_fact,
            binder_fact,
        )
        .expect_err("ambiguous");
    assert_eq!(invalid(&error), "ambiguous binder identity");
}

#[test]
fn binder_congruence_will_not_rename_the_binder() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let left_binder = fix.var(0);
    let right_binder = fix.var(1);
    let input = lam_at(&mut fix, left_binder, left_binder, arrow);
    let output = lam_at(&mut fix, right_binder, right_binder, arrow);

    let binder_fact = fix
        .syn_sub_var(None, left_binder, right_binder)
        .expect("sub var");
    let error = fix
        .syn_binder_congr(
            None,
            SynRel::Alpha,
            None,
            None,
            input,
            output,
            binder_fact,
            binder_fact,
        )
        .expect_err("renaming is `syn_alpha_binder`");
    assert_eq!(invalid(&error), "binder congruence");
}

#[test]
fn binder_congruence_needs_matching_binder_shapes() {
    let mut fix = Fix::new();
    let truth = fix.lit(true);
    let refl = fix.syn_refl(None, SynRel::Syn, truth).expect("reflexivity");
    let error = fix
        .syn_binder_congr(None, SynRel::Syn, None, None, truth, truth, refl, refl)
        .expect_err("not a binder");
    assert_eq!(invalid(&error), "binder congruence");
}

#[test]
fn alpha_renames_an_explicit_binder_and_records_a_row_equality() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let left_var = fix.var(1);
    let left = fix.lam(left_var, left_var).expect("identity");
    let right_var = fix.var(2);
    let right = fix.lam(right_var, right_var).expect("identity");
    let left_ty = fix.classifier(left).expect("function type");
    let right_ty = fix.classifier(right).expect("function type");
    merge(&mut fix, left_ty, right_ty);

    let classifier = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let body = fix.syn_sub_var(None, left_var, right_var).expect("sub var");
    let alpha = fix
        .syn_alpha_binder(None, left, right, classifier, body)
        .expect("alpha renaming");

    assert_eq!(fix.syn_fact(alpha).expect("minted").rel(), SynRel::Alpha);
    fix.union_syn_fact(alpha).expect("record the equality");
    assert!(fix.tm_eq(left, right).expect("resident"));
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn alpha_renaming_refuses_to_capture_a_free_occurrence() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let binder = fix.var(1);
    let free = fix.var(2);
    // `λ1. 2` cannot become `λ2. 2`: the rename would capture the free `2`.
    let left = fix.lam(binder, free).expect("abstraction");
    let right = fix.lam(free, free).expect("abstraction");

    let classifier = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let body = fix
        .syn_sub_leaf(None, binder, free, free)
        .expect("the body is a different variable");
    let error = fix
        .syn_alpha_binder(None, left, right, classifier, body)
        .expect_err("capture");
    assert_eq!(invalid(&error), "explicit alpha binder freshness");
}

#[test]
fn alpha_renaming_demands_alpha_equal_binder_classifiers() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let other_bool = fix.bool_ty(star).expect("second bool type");
    let left_var = fix.tm_fv(1, bool_ty).expect("variable");
    let right_var = fix.tm_fv(2, other_bool).expect("variable at the twin type");
    let left = fix.lam(left_var, left_var).expect("identity");
    let right = fix.lam(right_var, right_var).expect("identity");

    // Nothing yet relates the two `ty.bool` rows.
    let unrelated = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let body = fix.syn_sub_var(None, left_var, right_var);
    assert!(
        matches!(body, Err(KernelError::ClassifierMismatch { .. })),
        "the rename is blocked before the binder rule is even reached"
    );

    merge(&mut fix, bool_ty, other_bool);
    let body = fix
        .syn_sub_var(None, left_var, right_var)
        .expect("sub var after merging");
    let error = fix
        .syn_alpha_binder(None, left, right, unrelated, body)
        .expect_err("the classifier fact still names one row twice");
    assert_eq!(invalid(&error), "explicit alpha binder");
}

#[test]
fn alpha_renames_an_implicit_type_binder() {
    let mut fix = Fix::new();
    let star = fix.star;
    let truth = fix.lit(true);
    let left = fix.ty_exists(1, truth).expect("existential");
    let right = fix.ty_exists(2, truth).expect("existential");
    let left_binder = fix.ty_fv(1, star).expect("witness");
    let right_binder = fix.ty_fv(2, star).expect("witness");

    let body = fix
        .syn_sub_leaf(None, left_binder, right_binder, truth)
        .expect("the body is a literal");
    let id = fix
        .syn_alpha_implicit_binder(None, left, right, left_binder, right_binder, body)
        .expect("implicit alpha renaming");
    assert_eq!(fix.syn_fact(id).expect("minted").rel(), SynRel::Alpha);

    let left_model = fix.model(1, truth).expect("model");
    let right_model = fix.model(2, truth).expect("model");
    assert!(
        fix.syn_alpha_implicit_binder(
            None,
            left_model,
            right_model,
            left_binder,
            right_binder,
            body
        )
        .is_ok(),
        "alpha renaming is available under `Model`"
    );
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn an_implicit_binder_witness_must_name_the_stored_binder() {
    let mut fix = Fix::new();
    let star = fix.star;
    let truth = fix.lit(true);
    let existential = fix.ty_exists(1, truth).expect("existential");
    let wrong_name = fix.ty_fv(9, star).expect("witness for another name");
    let body = fix.syn_refl(None, SynRel::Syn, truth).expect("reflexivity");

    let error = fix
        .syn_implicit_binder_congr(
            None,
            SynRel::Syn,
            None,
            None,
            existential,
            existential,
            wrong_name,
            body,
        )
        .expect_err("wrong witness");
    assert_eq!(invalid(&error), "implicit binder witness");

    // The witness also has to be a type variable of kind `star`.
    let arrow_kind = fix.kind_arr(star, star).expect("arrow kind");
    let higher = fix.ty_fv(1, arrow_kind).expect("higher-kinded witness");
    assert!(matches!(
        fix.syn_implicit_binder_congr(
            None,
            SynRel::Syn,
            None,
            None,
            existential,
            existential,
            higher,
            body,
        ),
        Err(KernelError::WrongForm {
            expected: "kind.star",
            ..
        })
    ));
}

#[test]
fn conversion_congruence_stops_at_a_model_but_not_at_an_existential() {
    let mut fix = Fix::new();
    let star = fix.star;
    let truth = fix.lit(true);
    let model = fix.model(9, truth).expect("model");
    let existential = fix.ty_exists(9, truth).expect("existential");
    let witness = fix.ty_fv(9, star).expect("witness");

    for rel in [SynRel::Syn, SynRel::Alpha, SynRel::Conv] {
        let body = fix.syn_refl(None, rel, truth).expect("reflexivity");
        assert!(
            fix.syn_implicit_binder_congr(
                None,
                rel,
                None,
                None,
                existential,
                existential,
                witness,
                body
            )
            .is_ok(),
            "`tm.ty_exists` admits {rel:?}"
        );
        let result =
            fix.syn_implicit_binder_congr(None, rel, None, None, model, model, witness, body);
        if rel == SynRel::Conv {
            assert_eq!(
                invalid(&result.expect_err("model barrier")),
                "conversion under model"
            );
        } else {
            assert!(result.is_ok(), "`ty.model` admits {rel:?}");
        }
    }
}

#[test]
fn term_beta_reduces_a_redex_through_a_cached_substitution() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let binder = fix.var(0);
    let identity = fix.lam(binder, binder).expect("identity");
    let truth = fix.lit(true);
    let redex = fix.app(identity, truth).expect("application");

    let substitution = fix.syn_sub_var(None, binder, truth).expect("sub var");
    let beta = fix
        .tm_beta_fact(None, redex, substitution)
        .expect("term beta");
    let fact = fix.syn_fact(beta).expect("minted");
    assert_eq!(fact.rel(), SynRel::Conv);
    assert_eq!(fact.input(), redex);
    assert_eq!(fact.output(), truth);

    fix.union_syn_fact(beta).expect("record the equality");
    assert!(fix.tm_eq(redex, truth).expect("resident"));
    assert_eq!(fix.classifier(redex).expect("typed"), bool_ty);
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn family_beta_reduces_a_type_level_redex() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let binder = fix.ty_fv(1, star).expect("type variable");
    let family = fix.ty_lam(binder, binder).expect("identity family");
    let redex = fix.ty_app(family, bool_ty).expect("family application");

    let substitution = fix.syn_sub_var(None, binder, bool_ty).expect("sub var");
    let beta = fix
        .ty_beta_fact(None, redex, substitution)
        .expect("family beta");
    assert_eq!(fix.syn_fact(beta).expect("minted").output(), bool_ty);

    fix.union_syn_fact(beta).expect("record the equality");
    assert!(fix.ty_eq(redex, bool_ty).expect("resident"));
}

#[test]
fn beta_checks_the_redex_shape_and_the_substitution_endpoints() {
    let mut fix = Fix::new();
    let binder = fix.var(0);
    let identity = fix.lam(binder, binder).expect("identity");
    let truth = fix.lit(true);
    let falsity = fix.lit(false);
    let redex = fix.app(identity, truth).expect("application");
    let substitution = fix.syn_sub_var(None, binder, truth).expect("sub var");

    // Not an application.
    assert_eq!(
        invalid(
            &fix.tm_beta_fact(None, truth, substitution)
                .expect_err("not a redex")
        ),
        "term beta"
    );
    // The substitution has to replace exactly the redex's argument.
    let wrong = fix.syn_sub_var(None, binder, falsity).expect("sub var");
    assert_eq!(
        invalid(
            &fix.tm_beta_fact(None, redex, wrong)
                .expect_err("wrong value")
        ),
        "term beta"
    );
    // A direct fact carries no substitution at all.
    let direct = fix
        .syn_refl(None, SynRel::Conv, binder)
        .expect("reflexivity");
    assert_eq!(
        invalid(
            &fix.tm_beta_fact(None, redex, direct)
                .expect_err("not a substitution")
        ),
        "term beta"
    );
    // Category is checked before shape.
    assert!(matches!(
        fix.ty_beta_fact(None, redex, substitution),
        Err(KernelError::WrongCategory { .. })
    ));
}

#[test]
fn eta_contracts_a_lambda_whose_binder_is_used_exactly_once_at_the_end() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let function = fix.tm_fv(1, arrow).expect("function variable");
    let binder = fix.var(2);
    let body = fix.app(function, binder).expect("application");
    let source = lam_at(&mut fix, binder, body, arrow);

    let eta = fix.tm_eta_fact(None, source).expect("term eta");
    let fact = fix.syn_fact(eta).expect("minted");
    assert_eq!(fact.rel(), SynRel::Conv);
    assert_eq!(fact.output(), function);

    fix.union_syn_fact(eta).expect("record the equality");
    assert!(fix.tm_eq(source, function).expect("resident"));
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn eta_rejects_a_binder_that_still_occurs_in_the_function() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let arrow = fix.bool_arrow();
    let curried = fix.ty_arr(bool_ty, arrow).expect("bool -> bool -> bool");
    let outer = fix.tm_fv(1, curried).expect("curried function");
    let binder = fix.var(2);
    let function = fix.app(outer, binder).expect("partial application");
    let body = fix.app(function, binder).expect("application");
    let source = fix.lam(binder, body).expect("abstraction");

    let error = fix.tm_eta_fact(None, source).expect_err("binder occurs");
    assert_eq!(invalid(&error), "term eta");
}

#[test]
fn eta_rejects_an_argument_that_is_not_the_binder() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let function = fix.tm_fv(1, arrow).expect("function variable");
    let binder = fix.var(2);
    let other = fix.var(3);
    let body = fix.app(function, other).expect("application");
    let source = fix.lam(binder, body).expect("abstraction");

    assert_eq!(
        invalid(&fix.tm_eta_fact(None, source).expect_err("wrong argument")),
        "term eta"
    );

    // Neither is a non-lambda or a lambda whose body is not an application.
    let literal = fix.lit(true);
    assert_eq!(
        invalid(&fix.tm_eta_fact(None, literal).expect_err("not a lambda")),
        "term eta"
    );
    let constant = fix.lam(binder, literal).expect("constant function");
    assert_eq!(
        invalid(
            &fix.tm_eta_fact(None, constant)
                .expect_err("body is not an app")
        ),
        "term eta"
    );
}

#[test]
fn only_direct_facts_reach_the_row_union_find() {
    let mut fix = Fix::new();
    let binder = fix.var(0);
    let truth = fix.lit(true);
    let substitution = fix.syn_sub_var(None, binder, truth).expect("sub var");

    let error = fix
        .union_syn_fact(substitution)
        .expect_err("an active substitution is not an equality");
    assert_eq!(invalid(&error), "equality union");
    assert!(!fix.tm_eq(binder, truth).expect("resident"));
}

#[test]
fn a_long_derivation_keeps_every_slot_invariant() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let arrow = fix.bool_arrow();
    let function = fix.tm_fv(1, arrow).expect("function variable");
    let binder = fix.var(2);
    let free = fix.var(3);
    let truth = fix.lit(true);

    let mut ids: Vec<SynFactId> = Vec::new();
    ids.push(fix.syn_refl(None, SynRel::Syn, bool_ty).expect("refl"));
    ids.push(fix.syn_sub_var(None, free, truth).expect("sub var"));
    ids.push(
        fix.syn_sub_leaf(None, free, truth, function)
            .expect("sub leaf"),
    );
    let input = fix.app(function, free).expect("application");
    let output = fix.app(function, truth).expect("application");
    ids.push(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(free),
            Some(truth),
            input,
            output,
            &[ids[2], ids[1]],
        )
        .expect("congruence"),
    );
    ids.push(fix.syn_refine(None, ids[3], SynRel::Conv).expect("refine"));
    let identity = lam_at(&mut fix, binder, binder, arrow);
    let redex = fix.app(identity, truth).expect("application");
    let substitution = fix.syn_sub_var(None, binder, truth).expect("sub var");
    ids.push(fix.tm_beta_fact(None, redex, substitution).expect("beta"));
    ids.push(fix.syn_symm(None, ids[5]).expect("symmetry"));

    assert_cache_invariants(&fix.kernel);
    // Removing and reissuing slots must not disturb the surviving facts.
    assert!(fix.remove_syn_fact(ids[0]));
    assert!(fix.remove_syn_fact(ids[4]));
    assert_cache_invariants(&fix.kernel);
    fix.syn_refl(None, SynRel::Conv, truth).expect("reuse");
    fix.truncate_syn_facts(3);
    assert_cache_invariants(&fix.kernel);
}
