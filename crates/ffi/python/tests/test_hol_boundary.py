"""What the Python layer must never let through, and where it stops short.

The kernel's job is to make some conclusions unreachable. These tests attack
that boundary from userspace: they try to mint a false equality, to smuggle an
unchecked arena into a checked kernel, and to reuse evidence across kernels or
across a slot that has moved on. They also pin the places where the binding is
narrower than the Rust kernel, so closing a gap shows up as a test to update
rather than as silence.
"""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Kernel, Link
from hol_support import (
    basis,
    child_facts,
    fact_view,
    substitute,
    unify,
)

REJECTED = "does not establish"


def test_true_and_false_stay_apart_under_every_attempt() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    falsehood = base.literal(False)
    variable = base.var(1)

    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("syn", truth, falsehood, [])
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_congr("conv", truth, falsehood, [])
    with pytest.raises(ValueError, match=REJECTED):
        kernel.syn_sub_identity(
            variable,
            truth,
            truth,
            falsehood,
            kernel.syn_sub_var(variable, truth),
            kernel.syn_refl("syn", truth),
        )
    with pytest.raises(ValueError, match=REJECTED):
        kernel.union_syn_fact(kernel.syn_sub_var(variable, truth))

    # Reflexivity on either side is the only thing that goes in, and it is
    # already true.
    kernel.union_syn_fact(kernel.syn_refl("conv", truth))
    kernel.union_syn_fact(kernel.syn_refl("conv", falsehood))

    assert not kernel.equivalent(truth, falsehood)
    assert kernel.find(truth) == truth
    assert kernel.find(falsehood) == falsehood


def test_an_object_language_equation_is_not_a_kernel_equality() -> None:
    """`tm.eq` is a proposition; only `union_syn_fact` joins classes."""
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    falsehood = base.literal(False)

    equation = kernel.eq(base.bool_ty, truth, falsehood)
    kernel.add_context(equation)

    assert kernel.arena.context == [equation]
    assert not kernel.equivalent(truth, falsehood)


def test_a_beta_step_needs_evidence_for_the_substitution_it_claims() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    falsehood = base.literal(False)
    constant = kernel.lam(variable, truth)
    redex = kernel.app(constant, falsehood)

    # `(\\x. true) false` contracts to `true`, and only the fact that says so
    # is accepted.
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_beta(redex, kernel.syn_sub_var(variable, falsehood))

    contraction = kernel.tm_beta(redex, kernel.syn_sub_leaf(variable, falsehood, truth))
    kernel.union_syn_fact(contraction)

    assert kernel.equivalent(redex, truth)
    assert not kernel.equivalent(redex, falsehood)


def test_evidence_does_not_cross_kernels_even_at_the_same_slot() -> None:
    left, right = basis(), basis()
    left_truth = left.literal(True)
    right_truth = right.literal(True)
    left_fact = left.kernel.syn_refl("conv", left_truth)
    right_fact = right.kernel.syn_refl("conv", right_truth)

    assert left_fact.id == right_fact.id
    assert fact_view(left_fact) == fact_view(right_fact)
    with pytest.raises(ValueError, match="different kernel"):
        right.kernel.union_syn_fact(left_fact)
    with pytest.raises(ValueError, match="different kernel"):
        left.kernel.syn_trans(right_fact, left_fact)


def test_congruence_rejects_a_stale_child_handle() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    other = base.literal(True)
    falsehood = base.literal(False)

    stale = kernel.syn_refl("syn", truth)
    assert kernel.remove_syn_fact(stale)
    reused = kernel.syn_refl("syn", falsehood)
    assert reused.id == stale.id

    equation = kernel.eq(base.bool_ty, truth, truth)
    other_equation = kernel.eq(base.bool_ty, other, other)
    with pytest.raises(ValueError, match="overwritten slot"):
        kernel.syn_congr("syn", equation, other_equation, [stale, stale])


def test_a_kernel_cannot_be_seeded_from_unchecked_wire_data() -> None:
    nonsense = Arena()
    nonsense.bool(True)
    nonsense.add_axiom("ax.choice")
    nonsense.add_context(1)

    assert not hasattr(Kernel, "from_cbor")
    assert not hasattr(Kernel, "to_cbor")

    kernel = Kernel()
    kernel.import_literal(nonsense)

    # The import is recorded verbatim and contributes nothing checkable.
    assert len(kernel) == 0
    assert kernel.arena.axioms == []
    assert kernel.arena.context == []
    with pytest.raises(ValueError, match="does not name a kernel row"):
        kernel.category(1)


def test_editing_the_arena_copy_cannot_reach_back_into_the_kernel() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    falsehood = base.literal(False)

    forged = kernel.arena
    forged.add_context(truth)
    forged.add_axiom("ax.choice")
    forged.bool(True)

    assert not kernel.equivalent(truth, falsehood)
    assert kernel.arena.context == []
    assert kernel.arena.axioms == []
    assert len(kernel) == 4
    assert kernel.addr() != forged.addr()


def test_import_proxies_are_not_reachable_from_a_checked_kernel() -> None:
    """`kind_ref`, `ty_ref`, and `tm_ref` need a resolver with no binding yet.

    A kernel can record imports but never point at one, so its proxy rules are
    unreachable through this binding. Raw arenas expose the proxy constructors
    needed to test their wire representation.
    """
    assert all(hasattr(Arena, name) for name in ("kind_ref", "ty_ref", "tm_ref"))
    assert not any(hasattr(Kernel, name) for name in ("kind_ref", "ty_ref", "tm_ref"))

    kernel = Kernel()
    kernel.import_link(Link(O256.hash(b"unresolvable")))
    assert kernel.arena.definitions == []


def test_removal_reports_success_because_a_handle_is_checked_first() -> None:
    """The bool return can only be `True` here; a stale handle raises."""
    base = basis()
    kernel = base.kernel
    fact = kernel.syn_refl("syn", base.star)

    assert kernel.remove_syn_fact(fact) is True
    with pytest.raises(ValueError, match="is absent"):
        kernel.remove_syn_fact(fact)


def test_type_substitution_retypes_a_term() -> None:
    """Active substitution may transform a term's classifier."""
    base = basis()
    kernel = base.kernel
    parameter = kernel.ty_fv(1, base.star)
    typed = kernel.tm_fv(2, parameter)
    retyped = kernel.tm_fv(2, base.bool_ty)
    replacement = kernel.syn_sub_var(parameter, base.bool_ty)

    fact = kernel.syn_congr(
        "syn",
        typed,
        retyped,
        child_facts([replacement]),
        var=parameter,
        val=base.bool_ty,
    )
    assert fact_view(fact) == ("syn", parameter, base.bool_ty, typed, retyped)

    output, rebuilt = substitute(kernel, parameter, base.bool_ty, typed)
    assert output == retyped
    assert fact_view(rebuilt) == ("syn", parameter, base.bool_ty, typed, retyped)


def test_freshness_scanning_stays_conservative_under_shadowing() -> None:
    base = basis()
    kernel = base.kernel
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    binder = base.var(1)
    shadowing = kernel.tm_fv(1, function_ty)
    eta_shaped = kernel.lam(binder, kernel.app(shadowing, binder))

    # The function mentions the binder's name, so eta is refused even though
    # the two rows have different types.
    with pytest.raises(ValueError, match=REJECTED):
        kernel.tm_eta(eta_shaped)


def test_classes_stay_within_one_category_and_survive_long_chains() -> None:
    base = basis()
    kernel = base.kernel
    literals = [base.literal(True) for _ in range(24)]

    for left, right in zip(literals, literals[1:], strict=False):
        unify(kernel, left, right)

    root = kernel.find(literals[-1])
    assert root == literals[0]
    assert all(kernel.find(reference) == root for reference in literals)
    assert all(kernel.find_mut(reference) == root for reference in literals)
    assert kernel.equivalent(literals[0], literals[-1])
    assert not kernel.equivalent(literals[0], base.bool_ty)
    assert not kernel.equivalent(literals[0], base.star)


def test_a_kernel_that_refused_everything_is_unchanged() -> None:
    """A rejected rule must not leave a slot or a row behind."""
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    address = kernel.addr()
    rows = len(kernel)

    for attempt in (
        lambda: kernel.syn_congr("syn", truth, base.bool_ty, []),
        lambda: kernel.syn_symm(kernel.syn_refl("syn", truth), target=900),
        lambda: kernel.tm_eta(truth),
        lambda: kernel.add_axiom("ax.choice"),
        lambda: kernel.add_context(base.star),
        lambda: kernel.bool(base.star, True),
    ):
        with pytest.raises(ValueError):
            attempt()

    kernel.truncate_syn_facts(0)
    assert len(kernel) == rows
    assert kernel.addr() == address
