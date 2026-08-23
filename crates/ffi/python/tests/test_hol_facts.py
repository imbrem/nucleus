"""Syntactic facts are evidence, and every rule that makes one is small.

The fact table is a cache of checked claims about substitution, alpha
equivalence, and conversion. Nothing in it is searched for: a caller supplies
the endpoints and the evidence, and the kernel either agrees or refuses. These
tests exercise each rule from both sides.
"""

import pytest
from covalence.logic.hol import Kernel
from hol_support import (
    RELATIONS,
    assert_kernel_invariants,
    bool_kernel,
    congruent,
    fact_tuple,
    merge_congruent,
)


def function_kernel() -> tuple[Kernel, int, int, int]:
    """A kernel carrying `kind.star`, `ty.bool`, and `bool -> bool`."""
    kernel, star, bool_ty = bool_kernel()
    return kernel, star, bool_ty, kernel.ty_arr(bool_ty, bool_ty)


def test_reflexivity_holds_in_every_relation_and_category() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    for relation in RELATIONS:
        for reference in (star, bool_ty, truth):
            fact = kernel.syn_refl(relation, reference)
            assert fact_tuple(fact) == (relation, None, None, reference, reference)
    assert kernel.syn_fact_len() == len(RELATIONS) * 3
    assert_kernel_invariants(kernel)


@pytest.mark.parametrize("relation", ["", "Syn", "SYN", "beta", "eq", " syn"])
def test_unknown_relation_names_are_rejected(relation: str) -> None:
    kernel, star, bool_ty = bool_kernel()
    with pytest.raises(ValueError, match="relation must be"):
        kernel.syn_refl(relation, star)
    with pytest.raises(ValueError, match="relation must be"):
        kernel.syn_congr(relation, star, star, [])


def test_refinement_runs_one_way_along_syn_alpha_conv() -> None:
    kernel, star, bool_ty = bool_kernel()
    finer = {"syn": 0, "alpha": 1, "conv": 2}
    for source in RELATIONS:
        for target in RELATIONS:
            fact = kernel.syn_refl(source, star)
            if finer[source] <= finer[target]:
                assert kernel.syn_refine(fact, target).relation == target
            else:
                with pytest.raises(ValueError, match="relation refinement"):
                    kernel.syn_refine(fact, target)


def test_refinement_preserves_the_substitution_endpoints() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    substitution = kernel.syn_sub_var(variable, truth)
    refined = kernel.syn_refine(substitution, "conv")
    assert fact_tuple(refined) == ("conv", variable, truth, variable, truth)


def test_symmetry_reverses_direct_facts_only() -> None:
    kernel, star, bool_ty = bool_kernel()
    left = kernel.bool(bool_ty, True)
    right = kernel.bool(bool_ty, True)
    direct = congruent(kernel, left, right)
    assert fact_tuple(kernel.syn_symm(direct)) == ("syn", None, None, right, left)

    variable = kernel.tm_fv(1, bool_ty)
    active = kernel.syn_sub_var(variable, left)
    with pytest.raises(ValueError, match="symmetry"):
        kernel.syn_symm(active)


def test_transitivity_matches_the_middle_and_takes_the_coarser_relation() -> None:
    kernel, star, bool_ty = bool_kernel()
    first = kernel.bool(bool_ty, True)
    middle = kernel.bool(bool_ty, True)
    last = kernel.bool(bool_ty, True)
    left = congruent(kernel, first, middle)
    right = kernel.syn_congr("alpha", middle, last, [])
    assert fact_tuple(kernel.syn_trans(left, right)) == (
        "alpha",
        None,
        None,
        first,
        last,
    )

    disjoint = congruent(kernel, first, last)
    with pytest.raises(ValueError, match="transitivity"):
        kernel.syn_trans(disjoint, right)


def test_transitivity_carries_the_left_substitution_and_needs_a_direct_right() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    first = kernel.bool(bool_ty, True)
    second = kernel.bool(bool_ty, True)
    active = kernel.syn_sub_var(variable, first)
    equal_truths = congruent(kernel, first, second)

    composed = kernel.syn_trans(active, equal_truths)
    assert fact_tuple(composed) == ("syn", variable, first, variable, second)
    with pytest.raises(ValueError, match="transitivity"):
        kernel.syn_trans(active, active)


def test_the_variable_case_of_substitution() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    assert fact_tuple(kernel.syn_sub_var(variable, truth)) == (
        "syn",
        variable,
        truth,
        variable,
        truth,
    )

    with pytest.raises(ValueError, match="substitution variable"):
        kernel.syn_sub_var(truth, truth)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.syn_sub_var(variable, bool_ty)


def test_substitution_of_a_variable_checks_the_classifier() -> None:
    kernel, star, bool_ty = bool_kernel()
    other_ty = kernel.ty_arr(bool_ty, bool_ty)
    variable = kernel.tm_fv(1, bool_ty)
    mismatched = kernel.tm_fv(2, other_ty)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.syn_sub_var(variable, mismatched)


def test_type_variables_substitute_for_types() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.ty_fv(1, star)
    assert fact_tuple(kernel.syn_sub_var(variable, bool_ty)) == (
        "syn",
        variable,
        bool_ty,
        variable,
        bool_ty,
    )


def test_leaves_survive_substitution_untouched() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    other = kernel.tm_fv(2, bool_ty)

    for leaf in (star, bool_ty, truth, other):
        fact = kernel.syn_sub_leaf(variable, truth, leaf)
        assert fact_tuple(fact) == ("syn", variable, truth, leaf, leaf)


def test_a_leaf_rule_refuses_the_variable_being_replaced() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    shadow = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)

    with pytest.raises(ValueError, match="substitution leaf"):
        kernel.syn_sub_leaf(variable, truth, variable)
    # Same name, different row: still the variable being replaced.
    with pytest.raises(ValueError, match="substitution leaf"):
        kernel.syn_sub_leaf(variable, truth, shadow)


def test_a_leaf_rule_refuses_compound_rows() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    compound = kernel.eq(bool_ty, truth, truth)
    with pytest.raises(ValueError, match="substitution leaf"):
        kernel.syn_sub_leaf(variable, truth, compound)


def test_identity_substitution_needs_both_obligations() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(7, bool_ty)
    twin = kernel.tm_fv(7, bool_ty)
    truth = kernel.bool(bool_ty, True)
    variable_equality = congruent(kernel, variable, twin)
    body_equality = kernel.syn_refl("syn", truth)

    fact = kernel.syn_sub_identity(
        variable, twin, truth, truth, variable_equality, body_equality
    )
    assert fact_tuple(fact) == ("syn", variable, twin, truth, truth)

    wrong_body = kernel.syn_refl("syn", bool_ty)
    with pytest.raises(ValueError, match="identity substitution"):
        kernel.syn_sub_identity(
            variable, twin, truth, truth, variable_equality, wrong_body
        )
    with pytest.raises(ValueError, match="identity substitution"):
        kernel.syn_sub_identity(
            variable, twin, truth, truth, body_equality, body_equality
        )


def test_congruence_rebuilds_a_node_from_its_children() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    function = kernel.tm_fv(3, function_ty)
    variable = kernel.tm_fv(4, bool_ty)
    truth = kernel.bool(bool_ty, True)
    source = kernel.app(function, variable)
    target = kernel.app(function, truth)

    unchanged = kernel.syn_sub_leaf(variable, truth, function)
    replaced = kernel.syn_sub_var(variable, truth)
    fact = kernel.syn_congr(
        "syn", source, target, [unchanged.id, replaced.id], variable, truth
    )
    assert fact_tuple(fact) == ("syn", variable, truth, source, target)
    assert_kernel_invariants(kernel)


def test_congruence_checks_arity_head_and_child_evidence() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    twin = kernel.bool(bool_ty, True)
    falsity = kernel.bool(bool_ty, False)
    left = kernel.eq(bool_ty, truth, truth)
    right = kernel.eq(bool_ty, truth, twin)
    truth_refl = kernel.syn_refl("syn", truth)
    flip = congruent(kernel, truth, twin)

    with pytest.raises(ValueError, match="constructor congruence"):
        kernel.syn_congr("syn", left, right, [truth_refl.id])
    with pytest.raises(ValueError, match="constructor congruence"):
        kernel.syn_congr("syn", left, right, [truth_refl.id, truth_refl.id])
    assert (
        kernel.syn_congr("syn", left, right, [truth_refl.id, flip.id]).output == right
    )

    # `tm.bool` rows only share a head when they carry the same literal.
    with pytest.raises(ValueError, match="constructor congruence"):
        kernel.syn_congr("syn", truth, falsity, [])


def test_congruence_refuses_binders() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    left = kernel.lam(variable, variable)
    right = kernel.lam(variable, variable)
    refl = kernel.syn_refl("syn", variable)
    with pytest.raises(ValueError, match="constructor congruence"):
        kernel.syn_congr("syn", left, right, [refl.id, refl.id])


def test_congruence_requires_compatible_classifiers() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    truth = kernel.bool(bool_ty, True)
    other_bool = kernel.bool_ty(star)
    other_truth = kernel.bool(other_bool, True)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.syn_congr("syn", truth, other_truth, [])

    merge_congruent(kernel, bool_ty, other_bool)
    assert kernel.syn_congr("syn", truth, other_truth, []).output == other_truth


def test_a_partial_substitution_is_rejected() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    with pytest.raises(ValueError, match="partial substitution"):
        kernel.syn_congr("syn", truth, truth, [], None, truth)


def test_binder_congruence_rebuilds_under_an_unchanged_binder() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    left = kernel.lam(variable, variable)
    right = kernel.lam(variable, variable)
    merge_congruent(kernel, kernel.classifier(left), kernel.classifier(right))

    binder = kernel.syn_refl("syn", variable)
    fact = kernel.syn_binder_congr("syn", left, right, binder, binder)
    assert fact_tuple(fact) == ("syn", None, None, left, right)

    with pytest.raises(ValueError, match="binder congruence"):
        kernel.syn_binder_congr("syn", left, variable, binder, binder)
    assert_kernel_invariants(kernel)


def test_implicit_binder_congruence_covers_model_and_ty_exists() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    witness = kernel.ty_fv(9, star)
    body = kernel.syn_refl("syn", truth)

    for build in (kernel.model, kernel.ty_exists):
        left = build(9, truth)
        right = build(9, truth)
        fact = kernel.syn_implicit_binder_congr("syn", left, right, witness, body)
        assert fact_tuple(fact) == ("syn", None, None, left, right)

    mismatch = kernel.ty_fv(8, star)
    left = kernel.ty_exists(9, truth)
    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_implicit_binder_congr("syn", left, left, mismatch, body)


def test_conversion_never_enters_a_model() -> None:
    """`Model` is a guarded type; conversion under it is deliberately absent."""
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    model = kernel.model(9, truth)
    witness = kernel.ty_fv(9, star)

    conversion = kernel.syn_refl("conv", truth)
    with pytest.raises(ValueError, match="conversion under model"):
        kernel.syn_implicit_binder_congr("conv", model, model, witness, conversion)

    # The same shape is fine under `tyExists`, and fine at `syn` under `Model`.
    exists = kernel.ty_exists(9, truth)
    assert (
        kernel.syn_implicit_binder_congr(
            "conv", exists, exists, witness, conversion
        ).relation
        == "conv"
    )
    syntactic = kernel.syn_refl("syn", truth)
    assert (
        kernel.syn_implicit_binder_congr(
            "syn", model, model, witness, syntactic
        ).relation
        == "syn"
    )


def test_alpha_renaming_an_explicit_binder() -> None:
    kernel, star, bool_ty = bool_kernel()
    left_var = kernel.tm_fv(1, bool_ty)
    left = kernel.lam(left_var, left_var)
    right_var = kernel.tm_fv(2, bool_ty)
    right = kernel.lam(right_var, right_var)

    classifier = kernel.syn_refl("syn", bool_ty)
    merge_congruent(kernel, kernel.classifier(left), kernel.classifier(right))
    renamed = kernel.syn_sub_var(left_var, right_var)
    alpha = kernel.syn_alpha_binder(left, right, classifier, renamed)
    assert fact_tuple(alpha) == ("alpha", None, None, left, right)

    assert not kernel.equivalent(left, right)
    kernel.union_syn_fact(alpha)
    assert kernel.equivalent(left, right)
    assert_kernel_invariants(kernel)


def test_alpha_renaming_refuses_to_capture() -> None:
    """The new binder must not already occur free in the old body."""
    kernel, star, bool_ty = bool_kernel()
    captured = kernel.tm_fv(2, bool_ty)
    left_var = kernel.tm_fv(1, bool_ty)
    left = kernel.lam(left_var, captured)
    right = kernel.lam(captured, captured)
    classifier = kernel.syn_refl("syn", bool_ty)
    merge_congruent(kernel, kernel.classifier(left), kernel.classifier(right))
    body = kernel.syn_sub_leaf(left_var, captured, captured)
    with pytest.raises(ValueError, match="freshness"):
        kernel.syn_alpha_binder(left, right, classifier, body)


def test_alpha_renaming_an_implicit_binder() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    left = kernel.ty_exists(1, truth)
    right = kernel.ty_exists(2, truth)
    left_binder = kernel.ty_fv(1, star)
    right_binder = kernel.ty_fv(2, star)
    body = kernel.syn_sub_leaf(left_binder, right_binder, truth)

    fact = kernel.syn_alpha_implicit_binder(
        left, right, left_binder, right_binder, body
    )
    assert fact_tuple(fact) == ("alpha", None, None, left, right)

    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_alpha_implicit_binder(left, right, right_binder, left_binder, body)
    assert_kernel_invariants(kernel)


def test_term_beta_reduces_a_redex_it_can_see() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    identity = kernel.lam(variable, variable)
    truth = kernel.bool(bool_ty, True)
    redex = kernel.app(identity, truth)

    substitution = kernel.syn_sub_var(variable, truth)
    beta = kernel.tm_beta(redex, substitution)
    assert fact_tuple(beta) == ("conv", None, None, redex, truth)

    assert not kernel.equivalent(redex, truth)
    kernel.union_syn_fact(beta)
    assert kernel.equivalent(redex, truth)
    assert_kernel_invariants(kernel)


def test_term_beta_checks_the_shape_of_its_source() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    opaque = kernel.tm_fv(2, function_ty)
    substitution = kernel.syn_sub_var(variable, truth)

    with pytest.raises(ValueError, match="term beta"):
        kernel.tm_beta(truth, substitution)
    with pytest.raises(ValueError, match="term beta"):
        kernel.tm_beta(kernel.app(opaque, truth), substitution)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.tm_beta(bool_ty, substitution)


def test_term_beta_checks_that_the_evidence_is_the_right_substitution() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    other = kernel.tm_fv(2, bool_ty)
    identity = kernel.lam(variable, variable)
    truth = kernel.bool(bool_ty, True)
    falsity = kernel.bool(bool_ty, False)
    redex = kernel.app(identity, truth)

    with pytest.raises(ValueError, match="term beta"):
        kernel.tm_beta(redex, kernel.syn_sub_var(variable, falsity))
    with pytest.raises(ValueError, match="term beta"):
        kernel.tm_beta(redex, kernel.syn_sub_var(other, truth))


def test_type_beta_mirrors_term_beta() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.ty_fv(1, star)
    identity = kernel.ty_lam(variable, variable)
    redex = kernel.ty_app(identity, bool_ty)
    substitution = kernel.syn_sub_var(variable, bool_ty)

    beta = kernel.ty_beta(redex, substitution)
    assert fact_tuple(beta) == ("conv", None, None, redex, bool_ty)
    with pytest.raises(ValueError, match="declares Tm, but Ty was required"):
        kernel.ty_beta(kernel.bool(bool_ty, True), substitution)
    assert_kernel_invariants(kernel)


def test_eta_is_shape_and_freshness_only() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    function = kernel.tm_fv(1, function_ty)
    variable = kernel.tm_fv(2, bool_ty)
    source = kernel.lam(variable, kernel.app(function, variable))
    merge_congruent(kernel, kernel.classifier(source), function_ty)

    eta = kernel.tm_eta(source)
    assert fact_tuple(eta) == ("conv", None, None, source, function)
    kernel.union_syn_fact(eta)
    assert kernel.equivalent(source, function)
    assert_kernel_invariants(kernel)


def test_eta_refuses_a_binder_that_occurs_in_the_function() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    variable = kernel.tm_fv(2, bool_ty)
    other = kernel.tm_fv(3, bool_ty)
    capturing = kernel.lam(other, variable)
    source = kernel.lam(variable, kernel.app(capturing, variable))
    with pytest.raises(ValueError, match="term eta"):
        kernel.tm_eta(source)


def test_eta_checks_that_the_argument_is_the_binder() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    function = kernel.tm_fv(1, function_ty)
    variable = kernel.tm_fv(2, bool_ty)
    truth = kernel.bool(bool_ty, True)
    with pytest.raises(ValueError, match="term eta"):
        kernel.tm_eta(kernel.lam(variable, kernel.app(function, truth)))
    with pytest.raises(ValueError, match="term eta"):
        kernel.tm_eta(kernel.lam(variable, variable))


def test_only_direct_facts_reach_the_union_find() -> None:
    kernel, star, bool_ty = bool_kernel()
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    active = kernel.syn_sub_var(variable, truth)
    with pytest.raises(ValueError, match="equality union"):
        kernel.union_syn_fact(active)
    assert not kernel.equivalent(variable, truth)


def test_a_target_replaces_a_slot_in_place() -> None:
    kernel, star, bool_ty = bool_kernel()
    first = kernel.syn_refl("syn", star)
    second = kernel.syn_refl("syn", bool_ty)
    assert (first.id, second.id) == (1, 2)

    replaced = kernel.syn_refl("conv", bool_ty, first.id)
    assert replaced.id == first.id
    assert kernel.syn_fact_len() == 2
    assert fact_tuple(kernel.syn_fact(first.id)) == (
        "conv",
        None,
        None,
        bool_ty,
        bool_ty,
    )


def test_a_target_must_name_a_live_slot() -> None:
    kernel, star, bool_ty = bool_kernel()
    with pytest.raises(ValueError, match="is absent"):
        kernel.syn_refl("syn", star, 1)
    live = kernel.syn_refl("syn", star)
    kernel.remove_syn_fact(live)
    with pytest.raises(ValueError, match="is absent"):
        kernel.syn_refl("syn", star, live.id)


def test_removed_slots_are_reused_before_new_ones() -> None:
    kernel, star, bool_ty = bool_kernel()
    first = kernel.syn_refl("syn", star)
    second = kernel.syn_refl("syn", bool_ty)
    third = kernel.syn_refl("syn", star)
    assert kernel.remove_syn_fact(second) is True
    assert kernel.syn_fact_len() == 3

    reused = kernel.syn_refl("conv", bool_ty)
    assert reused.id == second.id
    assert kernel.syn_fact_len() == 3
    assert kernel.syn_fact(first.id).relation == "syn"
    assert kernel.syn_fact(third.id).relation == "syn"


def test_truncation_drops_a_temporary_suffix() -> None:
    kernel, star, bool_ty = bool_kernel()
    keep = kernel.syn_refl("syn", star)
    boundary = kernel.syn_fact_len()
    temporary = [kernel.syn_refl("conv", bool_ty) for _ in range(4)]

    kernel.truncate_syn_facts(boundary)
    assert kernel.syn_fact_len() == boundary
    assert kernel.syn_fact(keep.id).relation == "syn"
    for fact in temporary:
        with pytest.raises(ValueError, match="is absent"):
            kernel.syn_fact(fact.id)
    assert kernel.syn_refl("alpha", star).id == boundary + 1


def test_truncation_beyond_the_end_is_a_no_op_and_negatives_overflow() -> None:
    kernel, star, bool_ty = bool_kernel()
    kernel.syn_refl("syn", star)
    kernel.truncate_syn_facts(10**6)
    assert kernel.syn_fact_len() == 1
    with pytest.raises(OverflowError):
        kernel.truncate_syn_facts(-1)
    assert kernel.syn_fact_len() == 1


def test_facts_are_not_rows_and_rows_are_not_facts() -> None:
    kernel, star, bool_ty = bool_kernel()
    kernel.syn_refl("syn", star)
    assert len(kernel) == 2
    assert kernel.syn_fact_len() == 1
    with pytest.raises(ValueError, match="is absent"):
        kernel.syn_fact(2)


def universal_leaf(kernel: Kernel, var: int, reference: int):
    """A `var`-only fact that `reference` is unchanged by any replacement.

    There is no `syn_sub_leaf_forall` on the Python surface, so this rebuilds
    it out of zero-child congruence: a node congruent to itself under a
    substitution with no chosen value is exactly that claim.
    """
    definition = kernel.arena.definition(reference)
    children = [universal_leaf(kernel, var, child).id for child in definition.children]
    return kernel.syn_congr("syn", reference, reference, children, var)


def test_universal_substitution_facts_are_reachable() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    variable = kernel.tm_fv(4, bool_ty)
    function = kernel.tm_fv(3, function_ty)
    truth = kernel.bool(bool_ty, True)

    for leaf in (bool_ty, function, truth):
        fact = universal_leaf(kernel, variable, leaf)
        assert fact_tuple(fact) == ("syn", variable, None, leaf, leaf)


def test_universal_facts_compose_by_congruence_and_transitivity() -> None:
    """The Rust rule set's headline composition, driven from Python."""
    kernel, star, bool_ty, function_ty = function_kernel()
    function = kernel.tm_fv(3, function_ty)
    variable = kernel.tm_fv(4, bool_ty)
    first_truth = kernel.bool(bool_ty, True)
    second_truth = kernel.bool(bool_ty, True)
    first = kernel.app(function, first_truth)
    second = kernel.app(function, second_truth)

    universal = kernel.syn_congr(
        "syn",
        first,
        first,
        [
            universal_leaf(kernel, variable, function).id,
            universal_leaf(kernel, variable, first_truth).id,
        ],
        variable,
    )
    equal_applications = kernel.syn_congr(
        "syn",
        first,
        second,
        [
            kernel.syn_refl("syn", function).id,
            congruent(kernel, first_truth, second_truth).id,
        ],
    )
    composed = kernel.syn_trans(universal, equal_applications)
    assert fact_tuple(composed) == ("syn", variable, None, first, second)
    assert_kernel_invariants(kernel)


def test_a_universal_fact_is_not_a_direct_fact() -> None:
    kernel, star, bool_ty, function_ty = function_kernel()
    variable = kernel.tm_fv(4, bool_ty)
    truth = kernel.bool(bool_ty, True)
    universal = universal_leaf(kernel, variable, truth)

    with pytest.raises(ValueError, match="equality union"):
        kernel.union_syn_fact(universal)
    with pytest.raises(ValueError, match="symmetry"):
        kernel.syn_symm(universal)
