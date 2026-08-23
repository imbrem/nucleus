"""Attacks on the Ethane Python boundary, from outside the kernel.

Everything here is written as a caller who wants a theorem they have not
earned: reusing evidence across kernels, resurrecting handles whose slots were
recycled, feeding the checked layer arenas the raw layer was happy to build,
and hammering the API with sequences no well-behaved client would produce.

Two tests are marked expected-failure. Those are defects found while writing
this suite, kept as executable descriptions of the intended behaviour rather
than deleted or rewritten to assert the bug.
"""

import random

import pytest
from covalence.logic.hol import Arena, Kernel, Link
from hol_support import (
    assert_kernel_invariants,
    bool_kernel,
    call_names,
    congruent,
    fact_tuple,
    merge_congruent,
)


def loaded_kernel() -> tuple[Kernel, dict[str, int]]:
    """A kernel with enough rows for any rule to be attempted against it."""
    kernel, star, bool_ty = bool_kernel()
    function_ty = kernel.ty_arr(bool_ty, bool_ty)
    variable = kernel.tm_fv(1, bool_ty)
    truth = kernel.bool(bool_ty, True)
    falsity = kernel.bool(bool_ty, False)
    identity = kernel.lam(variable, variable)
    return kernel, {
        "star": star,
        "bool_ty": bool_ty,
        "function_ty": function_ty,
        "variable": variable,
        "truth": truth,
        "falsity": falsity,
        "identity": identity,
    }


# Every rule that consumes a `SynFact`, and how to call it with a hostile one.
FOREIGN_FACT_CALLS = [
    ("syn_refine", lambda kernel, fact: kernel.syn_refine(fact, "conv")),
    ("syn_symm", lambda kernel, fact: kernel.syn_symm(fact)),
    ("syn_trans.left", lambda kernel, fact: kernel.syn_trans(fact, fact)),
    (
        "syn_sub_identity.variable",
        lambda kernel, fact: kernel.syn_sub_identity(1, 1, 1, 1, fact, fact),
    ),
    (
        "syn_binder_congr",
        lambda kernel, fact: kernel.syn_binder_congr("syn", 1, 1, fact, fact),
    ),
    (
        "syn_implicit_binder_congr",
        lambda kernel, fact: kernel.syn_implicit_binder_congr("syn", 1, 1, 1, fact),
    ),
    (
        "syn_alpha_binder",
        lambda kernel, fact: kernel.syn_alpha_binder(1, 1, fact, fact),
    ),
    (
        "syn_alpha_implicit_binder",
        lambda kernel, fact: kernel.syn_alpha_implicit_binder(1, 1, 1, 1, fact),
    ),
    ("tm_beta", lambda kernel, fact: kernel.tm_beta(1, fact)),
    ("ty_beta", lambda kernel, fact: kernel.ty_beta(1, fact)),
    ("remove_syn_fact", lambda kernel, fact: kernel.remove_syn_fact(fact)),
    ("union_syn_fact", lambda kernel, fact: kernel.union_syn_fact(fact)),
]


@pytest.mark.parametrize(
    ("name", "call"),
    FOREIGN_FACT_CALLS,
    ids=call_names(FOREIGN_FACT_CALLS),
)
def test_evidence_does_not_travel_between_kernels(name: str, call) -> None:
    """A fact is a claim about one kernel's rows, and says nothing elsewhere."""
    victim, _ = loaded_kernel()
    attacker, _ = loaded_kernel()
    smuggled = attacker.syn_refl("conv", 1)

    with pytest.raises(ValueError, match="different kernel"):
        call(victim, smuggled)
    assert victim.syn_fact_len() == 0


@pytest.mark.parametrize(
    ("name", "call"),
    FOREIGN_FACT_CALLS,
    ids=call_names(FOREIGN_FACT_CALLS),
)
def test_evidence_does_not_survive_its_slot(name: str, call) -> None:
    """Slot numbers are recycled, so a handle carries its payload with it."""
    kernel, rows = loaded_kernel()
    stale = kernel.syn_refl("syn", rows["star"])
    kernel.remove_syn_fact(stale)
    replacement = kernel.syn_refl("conv", rows["bool_ty"])
    assert replacement.id == stale.id

    with pytest.raises(ValueError, match="overwritten slot"):
        call(kernel, stale)
    assert fact_tuple(kernel.syn_fact(stale.id)) == fact_tuple(replacement)


def test_a_handle_whose_slot_was_refilled_identically_still_works() -> None:
    """Identity is the kernel plus the payload, not the slot's history."""
    kernel, rows = loaded_kernel()
    original = kernel.syn_refl("syn", rows["star"])
    kernel.remove_syn_fact(original)
    twin = kernel.syn_refl("syn", rows["star"])
    assert twin.id == original.id
    assert kernel.syn_refine(original, "conv").relation == "conv"


def test_removing_evidence_twice_is_an_error_not_a_silent_no_op() -> None:
    kernel, rows = loaded_kernel()
    fact = kernel.syn_refl("syn", rows["star"])
    assert kernel.remove_syn_fact(fact) is True
    with pytest.raises(ValueError, match="is absent"):
        kernel.remove_syn_fact(fact)


@pytest.mark.xfail(
    reason="syn_congr children are slot numbers, not checked handles",
    strict=False,
)
def test_congruence_children_respect_the_handle_discipline() -> None:
    """A dead handle's number should be as dead as the handle.

    Every other rule takes a `SynFact` and re-checks its payload against the
    slot it names. `children` is a list of raw integers, so evidence a caller
    believes it is supplying is silently replaced by whatever now occupies the
    same slot. Marked expected-failure: taking handles here too would make the
    integer and the handle agree again.
    """
    kernel, rows = loaded_kernel()
    function = kernel.tm_fv(3, rows["function_ty"])
    argument = kernel.tm_fv(4, rows["bool_ty"])
    node = kernel.app(function, argument)

    stale = kernel.syn_refl("syn", function)
    argument_refl = kernel.syn_refl("syn", argument)
    kernel.remove_syn_fact(stale)
    assert kernel.syn_refl("conv", function).id == stale.id

    with pytest.raises(ValueError, match="overwritten slot"):
        kernel.syn_congr("conv", node, node, [stale.id, argument_refl.id])


def test_congruence_children_take_whatever_occupies_the_slot() -> None:
    """Today's behaviour, recorded so the defect above has a precise shape."""
    kernel, rows = loaded_kernel()
    function = kernel.tm_fv(3, rows["function_ty"])
    argument = kernel.tm_fv(4, rows["bool_ty"])
    node = kernel.app(function, argument)

    stale = kernel.syn_refl("syn", function)
    argument_refl = kernel.syn_refl("syn", argument)
    kernel.remove_syn_fact(stale)
    refilled = kernel.syn_refl("conv", function)
    assert refilled.id == stale.id

    # The handle is dead...
    with pytest.raises(ValueError, match="overwritten slot"):
        kernel.syn_refine(stale, "conv")
    # ...but its number is not, and it now names different evidence.
    reborn = kernel.syn_congr("conv", node, node, [stale.id, argument_refl.id])
    assert reborn.relation == "conv"
    assert_kernel_invariants(kernel)


def test_congruence_children_reject_absent_and_zero_slots() -> None:
    kernel, rows = loaded_kernel()
    equation = kernel.eq(rows["bool_ty"], rows["truth"], rows["truth"])
    with pytest.raises(ValueError, match="one-based"):
        kernel.syn_congr("syn", equation, equation, [0, 0])
    with pytest.raises(ValueError, match="is absent"):
        kernel.syn_congr("syn", equation, equation, [99, 99])


UNSOUND_ATTEMPTS = [
    ("distinct-literals", "constructor congruence"),
    ("beta-wrong-argument", "term beta"),
    ("eta-captured-binder", "term eta"),
    ("alpha-capture", "freshness"),
    ("conv-under-model", "conversion under model"),
    ("trans-broken-middle", "transitivity"),
    ("symm-of-substitution", "symmetry"),
    ("refine-conv-to-syn", "relation refinement"),
    ("leaf-is-the-variable", "substitution leaf"),
    ("union-of-substitution", "equality union"),
]


def _attempt(kernel: Kernel, rows: dict[str, int], name: str):
    star, bool_ty = rows["star"], rows["bool_ty"]
    truth, falsity = rows["truth"], rows["falsity"]
    variable, identity = rows["variable"], rows["identity"]
    if name == "distinct-literals":
        return lambda: kernel.syn_congr("syn", truth, falsity, [])
    if name == "beta-wrong-argument":
        redex = kernel.app(identity, truth)
        wrong = kernel.syn_sub_var(variable, falsity)
        return lambda: kernel.tm_beta(redex, wrong)
    if name == "eta-captured-binder":
        other = kernel.tm_fv(5, bool_ty)
        capturing = kernel.lam(other, variable)
        source = kernel.lam(variable, kernel.app(capturing, variable))
        return lambda: kernel.tm_eta(source)
    if name == "alpha-capture":
        captured = kernel.tm_fv(6, bool_ty)
        left = kernel.lam(variable, captured)
        right = kernel.lam(captured, captured)
        classifier = kernel.syn_refl("syn", bool_ty)
        merge_congruent(kernel, kernel.classifier(left), kernel.classifier(right))
        body = kernel.syn_sub_leaf(variable, captured, captured)
        return lambda: kernel.syn_alpha_binder(left, right, classifier, body)
    if name == "conv-under-model":
        model = kernel.model(7, truth)
        witness = kernel.ty_fv(7, star)
        body = kernel.syn_refl("conv", truth)
        return lambda: kernel.syn_implicit_binder_congr(
            "conv", model, model, witness, body
        )
    if name == "trans-broken-middle":
        twin = kernel.bool(bool_ty, True)
        left = congruent(kernel, truth, twin)
        right = kernel.syn_refl("syn", truth)
        return lambda: kernel.syn_trans(left, right)
    if name == "symm-of-substitution":
        active = kernel.syn_sub_var(variable, truth)
        return lambda: kernel.syn_symm(active)
    if name == "refine-conv-to-syn":
        conversion = kernel.syn_refl("conv", truth)
        return lambda: kernel.syn_refine(conversion, "syn")
    if name == "leaf-is-the-variable":
        return lambda: kernel.syn_sub_leaf(variable, truth, variable)
    if name == "union-of-substitution":
        active = kernel.syn_sub_var(variable, truth)
        return lambda: kernel.union_syn_fact(active)
    raise AssertionError(name)


@pytest.mark.parametrize(
    ("name", "message"),
    UNSOUND_ATTEMPTS,
    ids=[name for name, _ in UNSOUND_ATTEMPTS],
)
def test_a_rejected_rule_changes_nothing(name: str, message: str) -> None:
    """Refusal is total: no slot, no row, no equality, no address change."""
    kernel, rows = loaded_kernel()
    attempt = _attempt(kernel, rows, name)

    rows_before = len(kernel)
    slots_before = kernel.syn_fact_len()
    address_before = kernel.addr()
    equalities_before = {
        row.reference: kernel.find(row.reference) for row in kernel.arena.definitions
    }

    with pytest.raises(ValueError, match=message):
        attempt()

    assert len(kernel) == rows_before
    assert kernel.syn_fact_len() == slots_before
    assert kernel.addr() == address_before
    assert {
        row.reference: kernel.find(row.reference) for row in kernel.arena.definitions
    } == equalities_before
    assert_kernel_invariants(kernel)


def test_truth_and_falsity_never_join_one_class() -> None:
    """The headline unsoundness, attempted every way the API allows."""
    kernel, rows = loaded_kernel()
    truth, falsity = rows["truth"], rows["falsity"]

    for relation in ("syn", "alpha", "conv"):
        with pytest.raises(ValueError):
            kernel.union_syn_fact(kernel.syn_congr(relation, truth, falsity, []))
    with pytest.raises(ValueError):
        kernel.union_syn_fact(kernel.syn_refl("syn", truth, 1))

    reflexive = kernel.syn_refl("conv", truth)
    with pytest.raises(ValueError, match="transitivity"):
        kernel.syn_trans(reflexive, kernel.syn_refl("conv", falsity))
    assert not kernel.equivalent(truth, falsity)
    assert_kernel_invariants(kernel)


def test_discarding_evidence_cannot_discard_a_theorem() -> None:
    """The fact table is a cache; the union-find is the conclusion."""
    kernel, rows = loaded_kernel()
    twin = kernel.bool(rows["bool_ty"], True)
    fact = congruent(kernel, rows["truth"], twin)
    kernel.union_syn_fact(fact)
    assert kernel.equivalent(rows["truth"], twin)

    kernel.remove_syn_fact(fact)
    kernel.truncate_syn_facts(0)
    assert kernel.syn_fact_len() == 0
    assert kernel.equivalent(rows["truth"], twin)
    assert_kernel_invariants(kernel)


def test_the_fact_cache_leaks_into_the_content_address() -> None:
    """Evidence is part of the encoding, so the cache is part of the identity.

    Truncation restores the address exactly; removal does not, because a
    removed slot stays allocated as a free-list entry. Worth knowing before
    treating `addr()` as a hash of a kernel's logical content.
    """
    kernel, rows = loaded_kernel()
    baseline = kernel.addr()

    truncated = kernel.syn_refl("syn", rows["star"])
    assert kernel.addr() != baseline
    kernel.truncate_syn_facts(0)
    assert kernel.addr() == baseline

    removed = kernel.syn_refl("syn", rows["star"])
    kernel.remove_syn_fact(removed)
    assert kernel.syn_fact_len() == 1
    assert kernel.addr() != baseline
    kernel.truncate_syn_facts(0)
    assert kernel.addr() == baseline
    assert truncated.id == removed.id


def test_an_unvalidated_import_cannot_reach_the_checked_rows() -> None:
    """Importing is a naming operation; the kernel checks nothing about it."""
    hostile = Arena()
    hostile.kind_arr(999, 999)
    hostile.add_axiom("ax.choice")
    hostile.add_context(5)
    hostile.assert_valid(1)

    kernel, rows = loaded_kernel()
    before = len(kernel)
    kernel.import_literal(hostile)
    kernel.import_link(Link(hostile.addr()))

    assert len(kernel) == before
    assert kernel.arena.axioms == []
    assert kernel.arena.context == []
    assert kernel.arena.assertions == []
    assert_kernel_invariants(kernel)
    # And the kernel still has no way to name a row inside that import.
    assert not hasattr(kernel, "tm_ref")
    assert not hasattr(kernel, "ty_ref")
    assert not hasattr(kernel, "kind_ref")


def test_importing_a_kernel_snapshot_does_not_import_its_conclusions() -> None:
    proved, rows = loaded_kernel()
    twin = proved.bool(rows["bool_ty"], True)
    proved.union_syn_fact(congruent(proved, rows["truth"], twin))
    assert proved.equivalent(rows["truth"], twin)

    consumer, consumer_rows = loaded_kernel()
    consumer_twin = consumer.bool(consumer_rows["bool_ty"], True)
    assert consumer_twin == twin
    consumer.import_literal(proved.arena)

    # Same reference numbers, same syntax, different kernel: no shared equality.
    assert not consumer.equivalent(consumer_rows["truth"], consumer_twin)
    assert_kernel_invariants(consumer)


def test_reference_numbers_are_not_capabilities() -> None:
    """A number from one kernel means whatever it means in the other."""
    small, _, _ = bool_kernel()
    large, rows = loaded_kernel()
    assert len(large) > len(small)

    with pytest.raises(ValueError, match="does not name a kernel row"):
        small.category(rows["identity"])
    assert large.category(1) == small.category(1) == "kind"


def test_opaque_handles_are_not_accepted_where_references_are() -> None:
    """`Kind`, `Ty`, and `Tm` are outputs only; nothing consumes them."""
    kernel, rows = loaded_kernel()
    handle = kernel.ty(rows["bool_ty"])
    for call in (
        lambda: kernel.category(handle),
        lambda: kernel.classifier(handle),
        lambda: kernel.find(handle),
        lambda: kernel.bool(handle, True),
        lambda: kernel.syn_refl("syn", handle),
        lambda: kernel.add_context(handle),
    ):
        with pytest.raises(TypeError):
            call()


def test_a_fact_handle_is_not_a_slot_number() -> None:
    kernel, rows = loaded_kernel()
    fact = kernel.syn_refl("syn", rows["star"])
    with pytest.raises(TypeError):
        kernel.syn_congr("syn", rows["truth"], rows["truth"], [fact])
    with pytest.raises(TypeError):
        kernel.syn_fact(fact)
    with pytest.raises(TypeError):
        kernel.remove_syn_fact(fact.id)


def test_two_kernels_share_nothing() -> None:
    left, rows = loaded_kernel()
    right, _ = loaded_kernel()
    assert left.addr() == right.addr()

    twin = left.bool(rows["bool_ty"], True)
    left.union_syn_fact(congruent(left, rows["truth"], twin))
    assert left.addr() != right.addr()
    assert left.syn_fact_len() != right.syn_fact_len()
    assert not right.equivalent(rows["truth"], rows["falsity"])
    assert_kernel_invariants(right)


# Constructors safe to call with arbitrary existing references: each either
# appends a row or raises, and none can be made to do anything else.
def _random_step(kernel: Kernel, chance: random.Random) -> None:
    references = list(range(1, len(kernel) + 1))
    pick = lambda: chance.choice(references)  # noqa: E731
    slots = list(range(1, kernel.syn_fact_len() + 1))
    steps = [
        lambda: kernel.star(),
        lambda: kernel.kind_arr(pick(), pick()),
        lambda: kernel.bool_ty(pick()),
        lambda: kernel.ty_arr(pick(), pick()),
        lambda: kernel.ty_fv(chance.randrange(4), pick()),
        lambda: kernel.ty_app(pick(), pick()),
        lambda: kernel.ty_lam(pick(), pick()),
        lambda: kernel.tm_fv(chance.randrange(4), pick()),
        lambda: kernel.app(pick(), pick()),
        lambda: kernel.lam(pick(), pick()),
        lambda: kernel.bool(pick(), chance.choice([True, False])),
        lambda: kernel.eq(pick(), pick(), pick()),
        lambda: kernel.eps(pick(), pick()),
        lambda: kernel.model(chance.randrange(4), pick()),
        lambda: kernel.ty_exists(chance.randrange(4), pick()),
        lambda: kernel.add_context(pick()),
        lambda: kernel.syn_refl(chance.choice(["syn", "alpha", "conv"]), pick()),
        lambda: kernel.syn_sub_var(pick(), pick()),
        lambda: kernel.syn_sub_leaf(pick(), pick(), pick()),
        lambda: kernel.syn_congr(
            chance.choice(["syn", "alpha", "conv"]),
            pick(),
            pick(),
            [chance.choice(slots) for _ in range(chance.randrange(3))] if slots else [],
        ),
        lambda: kernel.tm_eta(pick()),
        lambda: (
            kernel.tm_beta(pick(), kernel.syn_fact(chance.choice(slots)))
            if slots
            else None
        ),
        lambda: (
            kernel.union_syn_fact(kernel.syn_fact(chance.choice(slots)))
            if slots
            else None
        ),
        lambda: (
            kernel.truncate_syn_facts(chance.randrange(len(slots) + 1))
            if slots
            else None
        ),
    ]
    try:
        chance.choice(steps)()
    except ValueError:
        pass  # A refusal is a correct outcome for almost all of these.


@pytest.mark.parametrize("seed", range(12))
def test_random_operation_sequences_keep_the_kernel_consistent(seed: int) -> None:
    """No sequence of public calls produces an inconsistent kernel.

    Most steps are expected to be refused; what matters is that a refusal
    leaves nothing behind, that accepted steps preserve every invariant, and
    that nothing escapes as a crash or as an error type callers cannot catch.
    """
    kernel, _, _ = bool_kernel()
    chance = random.Random(seed)
    for _ in range(200):
        _random_step(kernel, chance)
    assert_kernel_invariants(kernel)
    assert Arena.from_cbor(kernel.arena.to_cbor()).addr() == kernel.addr()
