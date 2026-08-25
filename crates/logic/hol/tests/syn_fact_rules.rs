//! The local LCF rules over the syntactic-fact cache: reflexivity, the
//! relation lattice, symmetry, transitivity, substitution leaves, and
//! constructor congruence.

mod support;

use covalence_logic_hol::{Kernel, KernelError, Ref, SynRel};
use support::{Fix, assert_cache_invariants, fact_id};

const RELATIONS: [SynRel; 3] = [SynRel::Syn, SynRel::Alpha, SynRel::Conv];

fn invalid(error: &KernelError) -> &'static str {
    match error {
        KernelError::InvalidSynFact { rule } => rule,
        other => panic!("expected a rejected local rule, got {other:?}"),
    }
}

#[test]
fn refinement_is_exactly_the_syn_alpha_conv_chain() {
    for (finer, coarser) in [
        (SynRel::Syn, SynRel::Syn),
        (SynRel::Syn, SynRel::Alpha),
        (SynRel::Syn, SynRel::Conv),
        (SynRel::Alpha, SynRel::Alpha),
        (SynRel::Alpha, SynRel::Conv),
        (SynRel::Conv, SynRel::Conv),
    ] {
        assert!(finer.refines(coarser), "{finer:?} must refine {coarser:?}");
    }
    for (coarser, finer) in [
        (SynRel::Alpha, SynRel::Syn),
        (SynRel::Conv, SynRel::Syn),
        (SynRel::Conv, SynRel::Alpha),
    ] {
        assert!(
            !coarser.refines(finer),
            "{coarser:?} must not refine {finer:?}"
        );
    }
}

#[test]
fn reflexivity_holds_in_every_relation_and_every_category() {
    let mut fix = Fix::new();
    let term = fix.lit(true);
    let rows = [fix.star, fix.bool_ty, term];
    for rel in RELATIONS {
        for row in rows {
            let id = fix.syn_refl(None, rel, row).expect("reflexivity");
            let fact = fix.syn_fact(id).expect("minted fact");
            assert_eq!(fact.rel(), rel);
            assert_eq!(fact.input(), row);
            assert_eq!(fact.output(), row);
            assert_eq!((fact.var(), fact.val()), (None, None));
        }
    }
}

#[test]
fn reflexivity_needs_a_resident_row() {
    let mut fix = Fix::new();
    let absent = Ref::new(500).expect("nonzero");
    assert!(matches!(
        fix.syn_refl(None, SynRel::Syn, absent),
        Err(KernelError::MissingDefinition { reference }) if reference == absent
    ));
}

#[test]
fn refinement_weakens_but_never_sharpens() {
    let mut fix = Fix::new();
    let star = fix.star;
    for source_rel in RELATIONS {
        for target_rel in RELATIONS {
            let source = fix.syn_refl(None, source_rel, star).expect("reflexivity");
            let result = fix.syn_refine(None, source, target_rel);
            assert_eq!(
                result.is_ok(),
                source_rel.refines(target_rel),
                "{source_rel:?} -> {target_rel:?}"
            );
            if let Ok(id) = result {
                assert_eq!(fix.syn_fact(id).expect("refined").rel(), target_rel);
            }
        }
    }
}

#[test]
fn refinement_carries_substitution_endpoints_along() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let value = fix.lit(true);
    let substitution = fix.syn_sub_var(None, variable, value).expect("sub var");
    let refined = fix
        .syn_refine(None, substitution, SynRel::Conv)
        .expect("refinement");

    let fact = fix.syn_fact(refined).expect("refined");
    assert_eq!(fact.var(), Some(variable));
    assert_eq!(fact.val(), Some(value));
    assert_eq!(fact.rel(), SynRel::Conv);
}

#[test]
fn symmetry_swaps_direct_endpoints_and_rejects_active_substitution() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let value = fix.lit(true);
    let direct = fix
        .syn_refl(None, SynRel::Alpha, variable)
        .expect("reflexivity");
    let flipped = fix.syn_symm(None, direct).expect("symmetry");
    assert_eq!(fix.syn_fact(flipped).expect("flipped").rel(), SynRel::Alpha);

    let substitution = fix.syn_sub_var(None, variable, value).expect("sub var");
    let error = fix.syn_symm(None, substitution).expect_err("rejected");
    assert_eq!(invalid(&error), "symmetry");
}

#[test]
fn transitivity_composes_to_the_coarser_relation() {
    let mut fix = Fix::new();
    let star = fix.star;
    for left_rel in RELATIONS {
        for right_rel in RELATIONS {
            let left = fix.syn_refl(None, left_rel, star).expect("reflexivity");
            let right = fix.syn_refl(None, right_rel, star).expect("reflexivity");
            let id = fix.syn_trans(None, left, right).expect("transitivity");
            let expected = if left_rel.refines(right_rel) {
                right_rel
            } else {
                left_rel
            };
            assert_eq!(fix.syn_fact(id).expect("composed").rel(), expected);
        }
    }
}

#[test]
fn transitivity_needs_the_middle_references_to_agree_exactly() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let left = fix.syn_refl(None, SynRel::Syn, star).expect("reflexivity");
    let right = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");

    let error = fix.syn_trans(None, left, right).expect_err("rejected");
    assert_eq!(invalid(&error), "transitivity");
}

#[test]
fn transitivity_carries_the_left_substitution_and_needs_a_direct_right() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let value = fix.lit(true);
    let substitution = fix.syn_sub_var(None, variable, value).expect("sub var");
    let direct = fix.syn_refl(None, SynRel::Syn, value).expect("reflexivity");

    // `[true / x] x = true` composed with `true = true` keeps the descriptor.
    let composed = fix
        .syn_trans(None, substitution, direct)
        .expect("transitivity");
    let fact = fix.syn_fact(composed).expect("minted");
    assert_eq!(fact.var(), Some(variable));
    assert_eq!(fact.val(), Some(value));
    assert_eq!(fact.input(), variable);
    assert_eq!(fact.output(), value);

    // The right-hand fact must be direct: there is no rule for composing two
    // substitutions.
    assert_eq!(
        invalid(
            &fix.syn_trans(None, direct, substitution)
                .expect_err("right")
        ),
        "transitivity"
    );
    let universal = fix
        .syn_sub_leaf_forall(None, variable, value)
        .expect("a literal is unchanged by every replacement");
    assert_eq!(
        invalid(
            &fix.syn_trans(None, direct, universal)
                .expect_err("universal right")
        ),
        "transitivity"
    );
}

#[test]
fn every_rule_rejects_a_missing_evidence_handle() {
    let mut fix = Fix::new();
    let star = fix.star;
    let absent = fact_id(7);
    let present = fix.syn_refl(None, SynRel::Syn, star).expect("reflexivity");

    let errors = [
        fix.syn_refine(None, absent, SynRel::Conv).unwrap_err(),
        fix.syn_symm(None, absent).unwrap_err(),
        fix.syn_trans(None, absent, present).unwrap_err(),
        fix.syn_trans(None, present, absent).unwrap_err(),
        fix.union_syn_fact(absent).unwrap_err(),
    ];
    for error in &errors {
        assert!(
            matches!(error, KernelError::MissingSynFact { id } if *id == absent),
            "expected a missing-slot error, got {error:?}"
        );
    }
}

#[test]
fn substitution_of_a_variable_is_the_primitive_case() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let value = fix.lit(true);
    let id = fix.syn_sub_var(None, variable, value).expect("sub var");

    let fact = fix.syn_fact(id).expect("minted");
    assert_eq!(fact.rel(), SynRel::Syn);
    assert_eq!(fact.var(), Some(variable));
    assert_eq!(fact.val(), Some(value));
    assert_eq!(fact.input(), variable);
    assert_eq!(fact.output(), value);
}

#[test]
fn substitution_needs_a_variable_and_a_compatible_replacement() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let value = fix.lit(true);

    // The target must be a free variable row.
    assert_eq!(
        invalid(&fix.syn_sub_var(None, value, value).expect_err("literal")),
        "substitution variable"
    );
    // The replacement must share the target's syntactic category.
    assert!(matches!(
        fix.syn_sub_var(None, variable, bool_ty),
        Err(KernelError::WrongCategory { .. })
    ));
    // And its classifier class.
    let other_star = fix.star().expect("second star");
    let alpha = fix.ty_fv(9, star).expect("type variable");
    assert!(matches!(
        fix.syn_sub_var(None, alpha, other_star),
        Err(KernelError::WrongCategory { .. })
    ));
}

#[test]
fn substitution_of_a_replacement_at_the_wrong_type_is_rejected() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let other_bool = fix.bool_ty(star).expect("second bool type");
    let variable = fix.tm_fv(0, bool_ty).expect("variable");
    let value = fix.bool(other_bool, true).expect("literal");

    // Duplicate `ty.bool` rows are distinct until userspace unions them.
    assert!(matches!(
        fix.syn_sub_var(None, variable, value),
        Err(KernelError::ClassifierMismatch { .. })
    ));

    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, bool_ty, other_bool)
        .expect("merge the duplicate type rows");
    assert!(fix.syn_sub_var(None, variable, value).is_ok());
}

#[test]
fn literal_leaves_are_invariant_under_every_substitution() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let value = fix.lit(true);
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let falsity = fix.lit(false);

    for leaf in [star, bool_ty, falsity] {
        let id = fix
            .syn_sub_leaf(None, variable, value, leaf)
            .expect("leaf substitution");
        let fact = fix.syn_fact(id).expect("minted");
        assert_eq!(fact.input(), leaf);
        assert_eq!(fact.output(), leaf);
        assert_eq!(fact.rel(), SynRel::Syn);
    }
}

#[test]
fn a_leaf_that_shares_the_target_name_is_never_unchanged() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let value = fix.lit(true);
    // A second row for the same name and type: still the same variable.
    let alias = fix.tm_fv(0, bool_ty).expect("alias");

    for target in [variable, alias] {
        let error = fix
            .syn_sub_leaf(None, variable, value, target)
            .expect_err("same name");
        assert_eq!(invalid(&error), "substitution leaf");
    }
}

#[test]
fn a_variable_leaf_is_unchanged_only_when_its_annotation_is_out_of_reach() {
    let mut fix = Fix::new();
    let star = fix.star;
    let alpha = fix.ty_fv(1, star).expect("type variable");
    let beta = fix.ty_fv(2, star).expect("type variable");

    // A type variable carries only a kind, and kinds hold no named syntax.
    assert!(fix.syn_sub_leaf(None, alpha, beta, beta).is_ok());
    // A `bool` term variable cannot mention `alpha` either.
    let at_bool = fix.var(3);
    assert!(fix.syn_sub_leaf(None, alpha, beta, at_bool).is_ok());
    // But a term variable annotated with `alpha` is not left alone by it.
    let at_alpha = fix.tm_fv(4, alpha).expect("z : α");
    assert_eq!(
        invalid(
            &fix.syn_sub_leaf(None, alpha, beta, at_alpha)
                .expect_err("the annotation is the target")
        ),
        "substitution leaf"
    );
}

#[test]
fn an_unresolved_proxy_is_never_a_substitution_leaf() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let value = fix.lit(true);

    let mut imported = Kernel::new();
    let imported_star = imported.star().expect("star");
    let imported_bool = imported.bool_ty(imported_star).expect("bool type");
    let foreign = imported.bool(imported_bool, true).expect("literal");
    let source = fix
        .import_literal(imported.into_arena())
        .expect("literal import");
    let proxy = fix
        .tm_ref(&mut support::Never, source, foreign, bool_ty)
        .expect("proxy");

    let error = fix
        .syn_sub_leaf(None, variable, value, proxy)
        .expect_err("opaque import");
    assert_eq!(invalid(&error), "substitution leaf");
}

#[test]
fn identity_substitution_reuses_a_proof_that_the_variable_is_the_value() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let twin = fix.tm_fv(0, bool_ty).expect("same name, same type");
    let body = fix.lit(true);

    let reflexive_type = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let variable_equality = fix
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            variable,
            twin,
            &[reflexive_type],
        )
        .expect("the two rows are literally the same variable");
    let body_equality = fix
        .syn_refl(None, SynRel::Alpha, body)
        .expect("reflexivity");

    let id = fix
        .syn_sub_identity(
            None,
            variable,
            twin,
            body,
            body,
            variable_equality,
            body_equality,
        )
        .expect("identity substitution");
    let fact = fix.syn_fact(id).expect("minted");
    assert_eq!(fact.rel(), SynRel::Alpha);
    assert_eq!(fact.var(), Some(variable));
    assert_eq!(fact.val(), Some(twin));
}

#[test]
fn identity_substitution_rejects_a_body_fact_with_other_endpoints() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let twin = fix.tm_fv(0, bool_ty).expect("same name, same type");
    let body = fix.lit(true);
    let other = fix.lit(false);

    let reflexive_type = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let variable_equality = fix
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            variable,
            twin,
            &[reflexive_type],
        )
        .expect("same variable");
    let body_equality = fix.syn_refl(None, SynRel::Syn, other).expect("reflexivity");

    let error = fix
        .syn_sub_identity(
            None,
            variable,
            twin,
            body,
            body,
            variable_equality,
            body_equality,
        )
        .expect_err("body endpoints disagree");
    assert_eq!(invalid(&error), "identity substitution");
}

#[test]
fn congruence_relates_children_at_the_requested_relation() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let left = fix.ty_arr(bool_ty, bool_ty).expect("arrow");
    let right = fix.ty_arr(bool_ty, bool_ty).expect("duplicate arrow");
    let child = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");

    for rel in RELATIONS {
        let id = fix
            .syn_congr(None, rel, None, None, left, right, &[child, child])
            .expect("congruence");
        assert_eq!(fix.syn_fact(id).expect("minted").rel(), rel);
    }
}

#[test]
fn congruence_checks_child_arity_and_child_endpoints() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let left = fix.ty_arr(bool_ty, bool_ty).expect("arrow");
    let right = fix.ty_arr(bool_ty, bool_ty).expect("duplicate arrow");
    let good = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");
    let star = fix.star;
    let wrong = fix.syn_refl(None, SynRel::Syn, star).expect("reflexivity");

    for children in [&[][..], &[good][..], &[good, good, good][..]] {
        let error = fix
            .syn_congr(None, SynRel::Syn, None, None, left, right, children)
            .expect_err("arity");
        assert_eq!(invalid(&error), "constructor congruence");
    }
    let error = fix
        .syn_congr(None, SynRel::Syn, None, None, left, right, &[wrong, good])
        .expect_err("endpoints");
    assert_eq!(invalid(&error), "constructor congruence");
}

#[test]
fn congruence_refuses_to_cross_a_binder() {
    let mut fix = Fix::new();
    let variable = fix.var(0);
    let left = fix.lam(variable, variable).expect("identity");
    let right = fix.lam(variable, variable).expect("duplicate identity");
    let child = fix
        .syn_refl(None, SynRel::Syn, variable)
        .expect("reflexivity");

    let error = fix
        .syn_congr(None, SynRel::Syn, None, None, left, right, &[child, child])
        .expect_err("binder");
    assert_eq!(invalid(&error), "constructor congruence");
}

#[test]
fn congruence_requires_the_same_constructor_payload() {
    let mut fix = Fix::new();
    let truth = fix.lit(true);
    let falsity = fix.lit(false);
    let star = fix.star;
    let bool_ty = fix.bool_ty;

    for (left, right) in [(truth, falsity), (star, bool_ty), (truth, bool_ty)] {
        let error = fix
            .syn_congr(None, SynRel::Syn, None, None, left, right, &[])
            .expect_err("different heads");
        assert_eq!(invalid(&error), "constructor congruence");
    }
}

#[test]
fn a_replacement_without_a_variable_is_reserved_wire_data() {
    let mut fix = Fix::new();
    let truth = fix.lit(true);
    let variable = fix.var(0);

    let error = fix
        .syn_congr(None, SynRel::Syn, None, Some(truth), truth, truth, &[])
        .expect_err("a value with nothing to replace");
    assert_eq!(invalid(&error), "partial substitution");

    // A variable without a value is the universal form, and is checked.
    assert!(
        fix.syn_congr(None, SynRel::Syn, Some(variable), None, truth, truth, &[])
            .is_ok()
    );
}

#[test]
fn a_universal_leaf_holds_for_every_compatible_replacement() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let other = fix.var(1);
    let truth = fix.lit(true);

    for leaf in [star, bool_ty, truth, other] {
        let id = fix
            .syn_sub_leaf_forall(None, variable, leaf)
            .expect("universal leaf");
        let fact = fix.syn_fact(id).expect("minted");
        assert_eq!(fact.var(), Some(variable));
        assert_eq!(fact.val(), None, "a universal fact names no replacement");
        assert_eq!(fact.input(), leaf);
        assert_eq!(fact.output(), leaf);
    }

    // The target itself is never unchanged, and neither is a proxy.
    assert_eq!(
        invalid(
            &fix.syn_sub_leaf_forall(None, variable, variable)
                .expect_err("same variable")
        ),
        "substitution leaf"
    );
    assert_eq!(
        invalid(
            &fix.syn_sub_leaf_forall(None, truth, truth)
                .expect_err("not a variable")
        ),
        "substitution variable"
    );
}

#[test]
fn a_universal_fact_survives_refinement_and_congruence() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let truth = fix.lit(true);
    let falsity = fix.lit(false);
    let equation = fix.eq(bool_ty, truth, falsity).expect("true = false");

    let left = fix
        .syn_sub_leaf_forall(None, variable, truth)
        .expect("universal leaf");
    let right = fix
        .syn_sub_leaf_forall(None, variable, falsity)
        .expect("universal leaf");
    let ty = fix
        .syn_sub_leaf_forall(None, variable, bool_ty)
        .expect("universal equality type");
    let congruence = fix
        .syn_congr(
            None,
            SynRel::Syn,
            Some(variable),
            None,
            equation,
            equation,
            &[ty, left, right],
        )
        .expect("congruence over a universal substitution");
    let refined = fix
        .syn_refine(None, congruence, SynRel::Conv)
        .expect("refinement");

    let fact = fix.syn_fact(refined).expect("minted");
    assert_eq!(fact.var(), Some(variable));
    assert_eq!(fact.val(), None);
    assert_eq!(fact.rel(), SynRel::Conv);

    // A universal fact is still not an equality between rows.
    assert_eq!(
        invalid(&fix.union_syn_fact(refined).expect_err("not direct")),
        "equality union"
    );
    assert_eq!(
        invalid(&fix.syn_symm(None, refined).expect_err("not direct")),
        "symmetry"
    );
    assert_cache_invariants(&fix.kernel);
}

#[test]
fn active_substitution_cannot_enter_an_opaque_proxy() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let value = fix.lit(true);

    let mut imported = Kernel::new();
    let imported_star = imported.star().expect("star");
    let imported_bool = imported.bool_ty(imported_star).expect("bool type");
    let foreign = imported.bool(imported_bool, true).expect("literal");
    let source = fix
        .import_literal(imported.into_arena())
        .expect("literal import");
    let proxy = fix
        .tm_ref(&mut support::Never, source, foreign, bool_ty)
        .expect("proxy");

    // Without a substitution the proxy is still reflexively equal to itself.
    assert!(
        fix.syn_congr(None, SynRel::Syn, None, None, proxy, proxy, &[])
            .is_ok()
    );
    let error = fix
        .syn_congr(
            None,
            SynRel::Syn,
            Some(variable),
            Some(value),
            proxy,
            proxy,
            &[],
        )
        .expect_err("opaque import");
    assert_eq!(invalid(&error), "constructor congruence");
}

#[test]
fn congruence_will_not_silently_skip_the_variable_case() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let variable = fix.var(0);
    let value = fix.lit(true);
    let child = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");

    // `[value / variable] variable` is `syn_sub_var`, never congruence.
    let error = fix
        .syn_congr(
            None,
            SynRel::Syn,
            Some(variable),
            Some(value),
            variable,
            variable,
            &[child],
        )
        .expect_err("same variable name");
    assert_eq!(invalid(&error), "constructor congruence");
}

#[test]
fn congruence_beneath_a_variable_compares_classifiers_literally() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let other_bool = fix.bool_ty(star).expect("second bool type");
    let left = fix.tm_fv(4, bool_ty).expect("variable");
    let right = fix.tm_fv(4, other_bool).expect("same name, other row");

    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, bool_ty, other_bool)
        .expect("merge the duplicate type rows");
    let alpha_child = fix
        .syn_refl(None, SynRel::Alpha, bool_ty)
        .expect("reflexivity");

    // A merely alpha-equal classifier is not enough beneath a variable row.
    let error = fix
        .syn_congr(None, SynRel::Alpha, None, None, left, right, &[alpha_child])
        .expect_err("classifier relation too coarse");
    assert_eq!(invalid(&error), "constructor congruence");

    let syn_child = fix
        .syn_congr(None, SynRel::Syn, None, None, bool_ty, other_bool, &[])
        .expect("the two rows really are the same type");
    assert!(
        fix.syn_congr(None, SynRel::Alpha, None, None, left, right, &[syn_child])
            .is_ok()
    );
}

#[test]
fn congruence_composes_a_substitution_without_walking_the_tree() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let function = fix.tm_fv(3, arrow).expect("function variable");
    let variable = fix.var(4);
    let value = fix.lit(true);
    let input = fix.app(function, variable).expect("application");
    let output = fix.app(function, value).expect("application");

    let unchanged = fix
        .syn_sub_leaf(None, variable, value, function)
        .expect("the function mentions no term variable");
    let replaced = fix.syn_sub_var(None, variable, value).expect("sub var");
    let id = fix
        .syn_congr(
            None,
            SynRel::Syn,
            Some(variable),
            Some(value),
            input,
            output,
            &[unchanged, replaced],
        )
        .expect("congruence");

    let fact = fix.syn_fact(id).expect("minted");
    assert_eq!(fact.input(), input);
    assert_eq!(fact.output(), output);
    assert_eq!(fact.var(), Some(variable));
}

#[test]
fn congruence_requires_endpoints_with_compatible_classifiers() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let other_bool = fix.bool_ty(star).expect("second bool type");
    let left = fix.bool(bool_ty, true).expect("literal");
    let right = fix
        .bool(other_bool, true)
        .expect("literal at the twin type");

    assert!(matches!(
        fix.syn_congr(None, SynRel::Syn, None, None, left, right, &[]),
        Err(KernelError::ClassifierMismatch { .. })
    ));

    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, bool_ty, other_bool)
        .expect("merge the duplicate type rows");
    assert!(
        fix.syn_congr(None, SynRel::Syn, None, None, left, right, &[])
            .is_ok()
    );
}

#[test]
fn a_target_slot_lets_a_rule_overwrite_its_own_evidence() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let scratch = fix.syn_refl(None, SynRel::Syn, star).expect("reflexivity");
    let other = fix
        .syn_refl(None, SynRel::Syn, bool_ty)
        .expect("reflexivity");

    let reused = fix
        .syn_trans(Some(scratch), scratch, scratch)
        .expect("in-place composition");
    assert_eq!(reused, scratch);
    assert_eq!(fix.syn_fact(scratch).expect("minted").input(), star);
    assert_eq!(fix.syn_fact_len(), 2);
    assert_eq!(fix.syn_fact(other).expect("untouched").input(), bool_ty);
}
