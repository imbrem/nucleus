"""The syntactic-fact rules, one test per line of the rule catalogue.

`docs/research/ethane-syn-facts.md` states each rule as a premise/conclusion
schema over `syn ⊑ alpha ⊑ conv`. These tests drive every rule the Python
kernel exposes, in both directions: the derivation the schema licenses, and
the near misses it does not. A rule that started accepting one of the negative
cases would be a soundness bug, not a convenience.
"""

import pytest
from hol_support import (
    CannotProveError,
    Rows,
    basis,
    beta,
    child_facts,
    fact_view,
    substitute,
    unify,
)

REJECTED = "does not establish"
ABSENT = "is absent"


def bool_pair(base) -> tuple[int, int]:
    """Two structurally identical Boolean literals in different rows."""
    return base.literal(True), base.literal(True)


# --- slot allocation ------------------------------------------------------


def test_slots_are_one_based_and_allocated_in_order() -> None:
    base = basis()
    kernel = base.kernel

    first = kernel.syn_refl("syn", base.star)
    second = kernel.syn_refl("alpha", base.bool_ty)

    assert (first.id, second.id) == (1, 2)
    assert kernel.syn_fact_len() == 2
    assert fact_view(kernel.syn_fact(first.id)) == fact_view(first)


def test_removal_frees_a_slot_for_the_next_allocation() -> None:
    base = basis()
    kernel = base.kernel
    first = kernel.syn_refl("syn", base.star)
    second = kernel.syn_refl("alpha", base.bool_ty)

    assert kernel.remove_syn_fact(first)
    # The table keeps the hole; the count is slots, not live facts.
    assert kernel.syn_fact_len() == 2
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_fact(first.id)

    reused = kernel.syn_refl("conv", base.bool_ty)
    assert reused.id == first.id
    assert reused.relation == "conv"
    assert kernel.syn_fact_len() == 2
    assert fact_view(kernel.syn_fact(second.id)) == fact_view(second)


def test_a_target_overwrites_only_an_occupied_slot() -> None:
    base = basis()
    kernel = base.kernel
    slot = kernel.syn_refl("syn", base.star)

    replaced = kernel.syn_refl("alpha", base.bool_ty, target=slot.id)
    assert replaced.id == slot.id
    assert fact_view(replaced) == ("alpha", None, None, base.bool_ty, base.bool_ty)
    assert kernel.syn_fact_len() == 1

    assert kernel.remove_syn_fact(replaced)
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_refl("syn", base.star, target=slot.id)
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_refl("syn", base.star, target=99)
    with pytest.raises(ValueError, match="one-based"):
        kernel.syn_refl("syn", base.star, target=0)


def test_truncation_keeps_a_prefix_and_is_total() -> None:
    base = basis()
    kernel = base.kernel
    keep = kernel.syn_refl("syn", base.star)
    temporary = kernel.syn_refl("alpha", base.bool_ty)

    kernel.truncate_syn_facts(99)
    assert kernel.syn_fact_len() == 2

    kernel.truncate_syn_facts(1)
    assert kernel.syn_fact_len() == 1
    assert fact_view(kernel.syn_fact(keep.id)) == fact_view(keep)
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_fact(temporary.id)

    kernel.truncate_syn_facts(0)
    assert kernel.syn_fact_len() == 0
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_fact(keep.id)


def test_truncation_rebuilds_the_free_list_over_the_prefix() -> None:
    base = basis()
    kernel = base.kernel
    first = kernel.syn_refl("syn", base.star)
    kernel.syn_refl("syn", base.bool_ty)
    third = kernel.syn_refl("syn", base.star)

    assert kernel.remove_syn_fact(first)
    assert kernel.remove_syn_fact(third)
    kernel.truncate_syn_facts(2)

    # Slot 3 is gone and slot 1 is the only hole left, so it is reused first.
    assert kernel.syn_refl("conv", base.star).id == first.id
    assert kernel.syn_refl("conv", base.star).id == 3
    assert kernel.syn_fact_len() == 3


def test_cache_operations_never_add_a_claim() -> None:
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)
    equal = kernel.syn_congr("syn", left, right, [])
    kernel.union_syn_fact(equal)
    address = kernel.addr()

    kernel.remove_syn_fact(equal)
    kernel.truncate_syn_facts(0)

    assert kernel.equivalent(left, right)
    assert kernel.addr() != address  # the table is part of the arena
    assert kernel.arena.eq[right - 1] == left
    assert kernel.arena.syn_eq[right - 1] == left
    assert kernel.arena.conv[right - 1] == left


# --- handle identity ------------------------------------------------------


def test_a_handle_is_rejected_by_a_different_kernel() -> None:
    left, right = basis(), basis()
    foreign = left.kernel.syn_refl("syn", left.star)

    with pytest.raises(ValueError, match="different kernel"):
        right.kernel.syn_refine(foreign, "alpha")
    with pytest.raises(ValueError, match="different kernel"):
        right.kernel.union_syn_fact(foreign)
    with pytest.raises(ValueError, match="different kernel"):
        right.kernel.remove_syn_fact(foreign)
    assert right.kernel.syn_refl("syn", right.star).id == 1


def test_a_handle_is_rejected_once_its_slot_has_moved_on() -> None:
    base = basis()
    kernel = base.kernel
    stale = kernel.syn_refl("syn", base.star)
    kernel.syn_refl("alpha", base.bool_ty, target=stale.id)

    with pytest.raises(ValueError, match="overwritten"):
        kernel.syn_refine(stale, "conv")
    with pytest.raises(ValueError, match="overwritten"):
        kernel.union_syn_fact(stale)


def test_a_removed_handle_reports_its_slot_as_absent() -> None:
    base = basis()
    kernel = base.kernel
    fact = kernel.syn_refl("syn", base.star)

    assert kernel.remove_syn_fact(fact)
    with pytest.raises(ValueError, match=ABSENT):
        kernel.remove_syn_fact(fact)
    with pytest.raises(ValueError, match=ABSENT):
        kernel.syn_refine(fact, "conv")


def test_congruence_evidence_uses_checked_handles() -> None:
    """Congruence applies the same ownership checks as every evidence rule."""
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)

    assert kernel.syn_congr("syn", left, right, [])
    with pytest.raises(TypeError):
        kernel.syn_congr("syn", left, right, [0])
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr(
            "syn", left, right, child_facts([kernel.syn_refl("syn", left)])
        )


# --- relation rules -------------------------------------------------------


@pytest.mark.parametrize("relation", ["syn", "alpha", "conv"])
def test_reflexivity_holds_in_every_relation(relation: str) -> None:
    base = basis()
    fact = base.kernel.syn_refl(relation, base.bool_ty)

    assert fact_view(fact) == (relation, None, None, base.bool_ty, base.bool_ty)


def test_reflexivity_needs_a_resident_row_and_a_known_relation() -> None:
    base = basis()

    with pytest.raises(ValueError, match="does not name a kernel row"):
        base.kernel.syn_refl("syn", 900)
    with pytest.raises(ValueError, match="relation must be"):
        base.kernel.syn_refl("equal", base.star)


@pytest.mark.parametrize(
    ("source", "target"),
    [("syn", "syn"), ("syn", "alpha"), ("syn", "conv"), ("alpha", "conv")],
)
def test_refinement_weakens_along_the_chain(source: str, target: str) -> None:
    base = basis()
    fact = base.kernel.syn_refine(base.kernel.syn_refl(source, base.star), target)

    assert fact.relation == target


@pytest.mark.parametrize(
    ("source", "target"),
    [("alpha", "syn"), ("conv", "syn"), ("conv", "alpha")],
)
def test_refinement_never_strengthens(source: str, target: str) -> None:
    base = basis()
    fact = base.kernel.syn_refl(source, base.star)

    with pytest.raises(ValueError, match=REJECTED):
        base.kernel.syn_refine(fact, target)


def test_refinement_copies_substitution_endpoints_unchanged() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    substitution = kernel.syn_sub_var(variable, truth)

    weakened = kernel.syn_refine(substitution, "conv")

    assert fact_view(weakened) == ("conv", variable, truth, variable, truth)


def test_symmetry_reverses_only_a_direct_fact() -> None:
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)
    direct = kernel.syn_congr("alpha", left, right, [])

    assert fact_view(kernel.syn_symm(direct)) == ("alpha", None, None, right, left)

    variable = base.var(1)
    substitution = kernel.syn_sub_var(variable, left)
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_symm(substitution)


def test_transitivity_matches_the_middle_reference_exactly() -> None:
    base = basis()
    kernel = base.kernel
    first, second = bool_pair(base)
    third = base.literal(True)
    left = kernel.syn_congr("syn", first, second, [])
    right = kernel.syn_congr("syn", second, third, [])

    assert fact_view(kernel.syn_trans(left, right)) == (
        "syn",
        None,
        None,
        first,
        third,
    )
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_trans(right, left)


def test_transitivity_takes_the_coarser_relation() -> None:
    base = basis()
    kernel = base.kernel
    first, second = bool_pair(base)
    third = base.literal(True)
    finer = kernel.syn_congr("syn", first, second, [])
    coarser = kernel.syn_congr("alpha", second, third, [])

    assert kernel.syn_trans(finer, coarser).relation == "alpha"
    assert kernel.syn_trans(coarser, kernel.syn_refl("syn", third)).relation == "alpha"


def test_transitivity_carries_the_left_substitution_and_needs_a_direct_right() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    first, second = bool_pair(base)
    substitution = kernel.syn_sub_var(variable, first)
    direct = kernel.syn_congr("syn", first, second, [])

    composed = kernel.syn_trans(substitution, direct)
    assert fact_view(composed) == ("syn", variable, first, variable, second)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_trans(direct, substitution)


# --- substitution rules ---------------------------------------------------


def test_the_variable_case_replaces_exactly_the_variable() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)

    fact = kernel.syn_sub_var(variable, truth)

    assert fact_view(fact) == ("syn", variable, truth, variable, truth)


def test_the_variable_case_needs_a_compatible_pair() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    function = kernel.tm_fv(2, kernel.ty_arr(base.bool_ty, base.bool_ty))

    with pytest.raises(ValueError, match="substitution variable"):
        kernel.syn_sub_var(truth, truth)
    with pytest.raises(ValueError, match="was required"):
        kernel.syn_sub_var(variable, base.bool_ty)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.syn_sub_var(variable, function)


def test_the_leaf_case_covers_exactly_the_catalogued_rows() -> None:
    base = basis()
    kernel = base.kernel
    term_variable = base.var(1)
    other_term_variable = base.var(2)
    truth = base.literal(True)
    type_variable = kernel.ty_fv(3, base.star)

    for leaf in (base.star, base.bool_ty, truth, other_term_variable, type_variable):
        fact = kernel.syn_sub_leaf(term_variable, truth, leaf)
        assert fact_view(fact) == ("syn", term_variable, truth, leaf, leaf)


def test_the_leaf_case_refuses_rows_substitution_must_enter() -> None:
    base = basis()
    kernel = base.kernel
    term_variable = base.var(1)
    truth = base.literal(True)
    type_variable = kernel.ty_fv(3, base.star)
    other_type_variable = kernel.ty_fv(4, base.star)
    term_at_type_variable = kernel.tm_fv(5, type_variable)
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)

    # The variable itself is replaced, not left alone.
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_leaf(term_variable, truth, term_variable)
    # A type substitution has to descend into a term variable's type child.
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_leaf(type_variable, other_type_variable, term_at_type_variable)
    # A term variable with an unrelated annotation is invariant.
    assert kernel.syn_sub_leaf(type_variable, other_type_variable, term_variable)
    # Compound rows are not leaves.
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_leaf(term_variable, truth, function_ty)


def test_a_same_named_variable_row_is_never_a_leaf() -> None:
    """Two rows spelling one variable would make substitution ambiguous."""
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    duplicate = base.var(1)
    truth = base.literal(True)

    assert variable != duplicate
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_leaf(variable, truth, duplicate)


def test_syntactic_identity_disables_a_substitution() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    duplicate = base.var(1)
    body, other_body = bool_pair(base)

    unify(kernel, variable, duplicate)
    identity = kernel.syn_congr(
        "syn", variable, duplicate, [kernel.syn_refl("syn", base.bool_ty)]
    )
    equal_bodies = kernel.syn_congr("syn", body, other_body, [])

    fact = kernel.syn_sub_identity(
        variable, duplicate, body, other_body, identity, equal_bodies
    )
    assert fact_view(fact) == ("syn", variable, duplicate, body, other_body)


def test_syntactic_identity_checks_both_premises() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    other = base.literal(True)
    wrong = kernel.syn_refl("syn", variable)
    bodies = kernel.syn_congr("syn", truth, other, [])

    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_identity(variable, truth, truth, other, wrong, bodies)


# --- congruence rules -----------------------------------------------------


def test_constructor_congruence_relates_matching_heads() -> None:
    base = basis()
    kernel = base.kernel
    left_argument, right_argument = bool_pair(base)
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function = kernel.tm_fv(1, function_ty)
    left = kernel.app(function, left_argument)
    right = kernel.app(function, right_argument)

    same_function = kernel.syn_refl("syn", function)
    equal_arguments = kernel.syn_congr("syn", left_argument, right_argument, [])
    fact = kernel.syn_congr(
        "syn", left, right, child_facts([same_function, equal_arguments])
    )

    assert fact_view(fact) == ("syn", None, None, left, right)


@pytest.mark.parametrize(
    ("relation", "child"),
    [("alpha", "syn"), ("conv", "syn"), ("conv", "alpha"), ("conv", "conv")],
)
def test_child_evidence_may_be_finer_than_the_parent(relation: str, child: str) -> None:
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)
    equal = kernel.syn_congr(child, left, right, [])
    equation_left = kernel.eq(base.bool_ty, left, left)
    equation_right = kernel.eq(base.bool_ty, right, right)
    equality_type = kernel.syn_refl(child, base.bool_ty)

    fact = kernel.syn_congr(
        relation,
        equation_left,
        equation_right,
        child_facts([equality_type, equal, equal]),
    )
    assert fact.relation == relation


def test_constructor_congruence_refuses_binders_and_mismatched_heads() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    lam = kernel.lam(variable, variable)
    refl = kernel.syn_refl("syn", variable)
    truth = base.literal(True)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("syn", lam, lam, child_facts([refl, refl]))
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("syn", truth, base.bool_ty, [])
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("syn", truth, base.literal(False), [])
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("syn", truth, truth, child_facts([refl]))


def test_substitution_congruence_refuses_the_variable_it_replaces() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    unchanged = kernel.syn_sub_leaf(variable, truth, base.bool_ty)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr(
            "syn", variable, variable, child_facts([unchanged]), var=variable, val=truth
        )


def test_a_reserved_payload_cannot_be_minted() -> None:
    """`val` without `var` has no checked meaning."""
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)

    with pytest.raises(ValueError, match="partial substitution"):
        kernel.syn_congr("syn", left, right, [], val=left)


def test_universal_facts_are_reachable_through_congruence() -> None:
    """`syn_sub_leaf_forall` is not bound, but the shape it mints is."""
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)

    universal = kernel.syn_congr("syn", truth, truth, [], var=variable)

    assert fact_view(universal) == ("syn", variable, None, truth, truth)
    # A universal premise composes with a direct one, keeping its endpoints.
    other = base.literal(True)
    equal = kernel.syn_congr("syn", truth, other, [])
    composed = kernel.syn_trans(universal, equal)
    assert fact_view(composed) == ("syn", variable, None, truth, other)


def test_binder_congruence_shadows_a_substitution_on_its_own_binder() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    lam = kernel.lam(variable, variable)

    fact = kernel.syn_binder_congr(
        "syn",
        lam,
        lam,
        kernel.syn_refl("syn", variable),
        kernel.syn_refl("syn", variable),
        var=variable,
        val=truth,
    )

    assert fact_view(fact) == ("syn", variable, truth, lam, lam)


def test_binder_congruence_crosses_a_different_binder() -> None:
    base = basis()
    kernel = base.kernel
    replaced = base.var(1)
    binder = base.var(2)
    truth = base.literal(True)
    source = kernel.lam(binder, replaced)
    target = kernel.lam(binder, truth)
    unify(kernel, kernel.classifier(source), kernel.classifier(target))

    fact = kernel.syn_binder_congr(
        "syn",
        source,
        target,
        kernel.syn_refl("syn", binder),
        kernel.syn_sub_var(replaced, truth),
        var=replaced,
        val=truth,
    )

    assert fact_view(fact) == ("syn", replaced, truth, source, target)


def test_binder_congruence_refuses_a_capturing_replacement() -> None:
    base = basis()
    kernel = base.kernel
    replaced = base.var(1)
    binder = base.var(2)
    source = kernel.lam(binder, replaced)
    target = kernel.lam(binder, binder)

    with pytest.raises(ValueError, match="binder freshness"):
        kernel.syn_binder_congr(
            "syn",
            source,
            target,
            kernel.syn_refl("syn", binder),
            kernel.syn_sub_var(replaced, binder),
            var=replaced,
            val=binder,
        )


def test_binder_congruence_refuses_an_ambiguous_binder() -> None:
    """Same name, different classifier row: the kernel cannot tell them apart.

    Binder identity is the pair `(name, classifier reference)`, so two rows
    whose classifiers merely became equivalent still spell one name twice.
    """
    base = basis()
    kernel = base.kernel
    duplicate_bool = kernel.bool_ty(base.star)
    unify(kernel, base.bool_ty, duplicate_bool)
    binder = kernel.tm_fv(1, base.bool_ty)
    replaced = kernel.tm_fv(1, duplicate_bool)
    truth = base.literal(True)
    source = kernel.lam(binder, replaced)

    with pytest.raises(ValueError, match="ambiguous binder identity"):
        kernel.syn_binder_congr(
            "syn",
            source,
            source,
            kernel.syn_refl("syn", binder),
            kernel.syn_refl("syn", replaced),
            var=replaced,
            val=truth,
        )


def test_a_binder_shadowing_needs_the_same_typed_variable() -> None:
    """Identity is by reference to the classifier, not by equality class."""
    base = basis()
    kernel = base.kernel
    binder = base.var(1)
    truth = base.literal(True)
    source = kernel.lam(binder, binder)

    fact = kernel.syn_binder_congr(
        "syn",
        source,
        source,
        kernel.syn_refl("syn", binder),
        kernel.syn_refl("syn", binder),
        var=binder,
        val=truth,
    )
    assert fact_view(fact) == ("syn", binder, truth, source, source)


def test_implicit_binder_congruence_needs_a_star_kinded_witness() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    quantified = kernel.ty_exists(9, truth)
    body = kernel.syn_refl("syn", truth)

    assert kernel.syn_implicit_binder_congr(
        "syn", quantified, quantified, kernel.ty_fv(9, base.star), body
    )
    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_implicit_binder_congr(
            "syn", quantified, quantified, kernel.ty_fv(8, base.star), body
        )
    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_implicit_binder_congr(
            "syn", quantified, quantified, base.var(9), body
        )
    arrow = kernel.kind_arr(base.star, base.star)
    with pytest.raises(ValueError, match="kind.star was required"):
        kernel.syn_implicit_binder_congr(
            "syn", quantified, quantified, kernel.ty_fv(9, arrow), body
        )


def test_conversion_never_enters_a_model() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    model = kernel.model(9, truth)
    quantified = kernel.ty_exists(9, truth)
    witness = kernel.ty_fv(9, base.star)
    body = kernel.syn_refl("conv", truth)

    with pytest.raises(ValueError, match="conversion under model"):
        kernel.syn_implicit_binder_congr("conv", model, model, witness, body)
    # The same shape is fine under `ty_exists`, and `syn` is fine under `Model`.
    assert kernel.syn_implicit_binder_congr(
        "conv", quantified, quantified, witness, body
    )
    assert kernel.syn_implicit_binder_congr(
        "syn", model, model, witness, kernel.syn_refl("syn", truth)
    )


# --- alpha rules ----------------------------------------------------------


def test_alpha_renames_an_explicit_binder() -> None:
    base = basis()
    kernel = base.kernel
    left_binder = base.var(1)
    right_binder = base.var(2)
    left = kernel.lam(left_binder, left_binder)
    right = kernel.lam(right_binder, right_binder)
    unify(kernel, kernel.classifier(left), kernel.classifier(right))

    classifier = kernel.syn_refl("syn", base.bool_ty)
    body = kernel.syn_sub_var(left_binder, right_binder)
    fact = kernel.syn_alpha_binder(left, right, classifier, body)

    assert fact_view(fact) == ("alpha", None, None, left, right)
    kernel.union_syn_fact(fact)
    assert kernel.equivalent(left, right)


def test_alpha_refuses_a_binder_that_would_capture() -> None:
    base = basis()
    kernel = base.kernel
    left_binder = base.var(1)
    free = base.var(2)
    left = kernel.lam(left_binder, free)
    right = kernel.lam(free, free)
    unify(kernel, kernel.classifier(left), kernel.classifier(right))

    classifier = kernel.syn_refl("syn", base.bool_ty)
    body = kernel.syn_sub_leaf(left_binder, free, free)
    with pytest.raises(ValueError, match="alpha binder freshness"):
        kernel.syn_alpha_binder(left, right, classifier, body)


def test_alpha_renames_an_implicit_binder() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    left = kernel.ty_exists(1, truth)
    right = kernel.ty_exists(2, truth)
    left_witness = kernel.ty_fv(1, base.star)
    right_witness = kernel.ty_fv(2, base.star)

    body = kernel.syn_sub_leaf(left_witness, right_witness, truth)
    fact = kernel.syn_alpha_implicit_binder(
        left, right, left_witness, right_witness, body
    )

    assert fact_view(fact) == ("alpha", None, None, left, right)


def test_alpha_implicit_binder_checks_both_witnesses() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    left = kernel.ty_exists(1, truth)
    right = kernel.ty_exists(2, truth)
    left_witness = kernel.ty_fv(1, base.star)
    right_witness = kernel.ty_fv(2, base.star)
    wrong_witness = kernel.ty_fv(3, base.star)
    body = kernel.syn_sub_leaf(left_witness, right_witness, truth)

    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_alpha_implicit_binder(
            left, right, wrong_witness, right_witness, body
        )
    with pytest.raises(ValueError, match="implicit binder witness"):
        kernel.syn_alpha_implicit_binder(left, right, left_witness, wrong_witness, body)


# --- root conversion rules ------------------------------------------------


def test_term_beta_contracts_a_root_redex() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    identity = kernel.lam(variable, variable)
    redex = kernel.app(identity, truth)

    substitution = kernel.syn_sub_var(variable, truth)
    fact = kernel.tm_beta(redex, substitution)

    assert fact_view(fact) == ("conv", None, None, redex, truth)
    assert not kernel.equivalent(redex, truth)
    kernel.union_syn_fact(fact)
    assert kernel.equivalent(redex, truth)


def test_term_beta_checks_the_shape_and_the_evidence() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    falsehood = base.literal(False)
    identity = kernel.lam(variable, variable)
    redex = kernel.app(identity, truth)
    opaque = kernel.tm_fv(2, kernel.ty_arr(base.bool_ty, base.bool_ty))
    not_a_redex = kernel.app(opaque, truth)
    substitution = kernel.syn_sub_var(variable, truth)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_beta(truth, substitution)
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_beta(not_a_redex, substitution)
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_beta(redex, kernel.syn_sub_var(variable, falsehood))
    with pytest.raises(ValueError, match="was required"):
        kernel.ty_beta(redex, substitution)


def test_type_beta_contracts_a_type_family_redex() -> None:
    base = basis()
    kernel = base.kernel
    parameter = kernel.ty_fv(1, base.star)
    family = kernel.ty_lam(parameter, parameter)
    redex = kernel.ty_app(family, base.bool_ty)

    substitution = kernel.syn_sub_var(parameter, base.bool_ty)
    fact = kernel.ty_beta(redex, substitution)

    assert fact_view(fact) == ("conv", None, None, redex, base.bool_ty)


def test_eta_accepts_only_the_exact_shape() -> None:
    base = basis()
    kernel = base.kernel
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function = kernel.tm_fv(1, function_ty)
    variable = base.var(2)
    other = base.var(3)
    source = kernel.lam(variable, kernel.app(function, variable))
    unify(kernel, kernel.classifier(source), function_ty)

    fact = kernel.tm_eta(source)
    assert fact_view(fact) == ("conv", None, None, source, function)

    wrong_argument = kernel.lam(variable, kernel.app(function, other))
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_eta(wrong_argument)
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_eta(kernel.lam(variable, variable))
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_eta(function)


def test_eta_refuses_a_function_mentioning_the_binder() -> None:
    base = basis()
    kernel = base.kernel
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    variable = base.var(2)
    shadowing = kernel.tm_fv(2, function_ty)
    source = kernel.lam(variable, kernel.app(shadowing, variable))

    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_eta(source)


# --- union ----------------------------------------------------------------


@pytest.mark.parametrize("relation", ["syn", "alpha", "conv"])
def test_union_accepts_every_direct_relation(relation: str) -> None:
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)

    kernel.union_syn_fact(kernel.syn_congr(relation, left, right, []))

    assert kernel.equivalent(left, right)


def test_union_refuses_a_substitution_fact() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.union_syn_fact(kernel.syn_sub_var(variable, truth))
    assert not kernel.equivalent(variable, truth)


def test_union_is_idempotent_and_keeps_categories_apart() -> None:
    base = basis()
    kernel = base.kernel
    left, right = bool_pair(base)
    fact = kernel.syn_congr("syn", left, right, [])

    kernel.union_syn_fact(fact)
    kernel.union_syn_fact(fact)

    assert kernel.equivalent(left, right)
    assert not kernel.equivalent(left, base.bool_ty)


# --- derivations built out of the rules -----------------------------------


def test_a_nested_redex_reduces_through_the_helper_prover() -> None:
    base = basis()
    kernel = base.kernel
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function = kernel.tm_fv(1, function_ty)
    variable = base.var(2)
    twice = kernel.lam(variable, kernel.app(function, kernel.app(function, variable)))
    truth = base.literal(True)
    redex = kernel.app(twice, truth)

    contractum, fact = beta(kernel, redex)
    kernel.union_syn_fact(fact)
    rows = Rows(kernel)

    assert fact.relation == "conv"
    assert kernel.equivalent(redex, contractum)
    assert rows[contractum].tag == "tm.app"
    inner = rows[contractum].children[1]
    assert rows[inner].children == [function, truth]


def test_substitution_leaves_a_shadowed_binder_alone() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    shadowed = kernel.lam(variable, variable)

    output, fact = substitute(kernel, variable, truth, shadowed)

    assert output == shadowed
    assert fact_view(fact) == ("syn", variable, truth, shadowed, shadowed)


def test_the_prover_refuses_to_capture() -> None:
    base = basis()
    kernel = base.kernel
    replaced = base.var(1)
    binder = base.var(2)
    source = kernel.lam(binder, replaced)

    with pytest.raises(CannotProveError, match="captured"):
        substitute(kernel, replaced, binder, source)
