"""The userspace prover in `hol_support`, exercised on its own.

The kernel has no proof search, so anything that walks a term and emits rules
lives outside it. These tests cover the helper the rest of the suite leans on:
what it derives, what it shares rather than rebuilds, and where it declines.
"""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Link
from hol_support import (
    CannotProveError,
    Rows,
    arena_view,
    basis,
    beta,
    definition_view,
    fact_view,
    link_view,
    meta_view,
    prove_congruence,
    substitute,
    unify,
)


def test_views_compare_snapshots_that_have_no_equality_of_their_own() -> None:
    arena = Arena()
    star = arena.kind_star()
    duplicate = Arena()
    duplicate.kind_star()
    source = arena.add_null_import()
    arena.assume_wf(source, star, star)

    row, other_row = arena.definition(star), duplicate.definition(star)
    assert row is not other_row
    assert row != other_row
    assert definition_view(row) == definition_view(other_row)

    address = O256.hash(b"link")
    assert Link(address) != Link(address)
    assert link_view(Link(address)) == link_view(Link(address))
    assert meta_view(arena.assumptions[0]) == ("meta.wf", source, star, star)
    assert arena_view(arena) != arena_view(duplicate)


def test_congruence_unions_the_classifiers_it_needs_on_the_way_up() -> None:
    base = basis()
    kernel = base.kernel
    left_domain = kernel.ty_arr(base.bool_ty, base.bool_ty)
    right_domain = kernel.ty_arr(base.bool_ty, base.bool_ty)
    left = kernel.tm_fv(1, left_domain)
    right = kernel.tm_fv(1, right_domain)

    assert not kernel.equivalent(left_domain, right_domain)
    fact = prove_congruence(kernel, left, right)

    assert fact_view(fact) == ("syn", None, None, left, right)
    assert kernel.equivalent(left_domain, right_domain)


def test_congruence_declines_rows_that_spell_different_expressions() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)

    with pytest.raises(CannotProveError, match="is not"):
        prove_congruence(kernel, truth, base.bool_ty)
    with pytest.raises(CannotProveError, match="different payloads"):
        prove_congruence(kernel, truth, base.literal(False))
    with pytest.raises(CannotProveError, match="different payloads"):
        prove_congruence(kernel, base.var(1), base.var(2))


def test_unify_puts_structurally_equal_rows_in_one_class() -> None:
    base = basis()
    kernel = base.kernel
    left = kernel.eq(base.bool_ty, base.literal(True), base.literal(True))
    right = kernel.eq(base.bool_ty, base.literal(True), base.literal(True))

    unify(kernel, left, right)

    assert kernel.equivalent(left, right)
    assert kernel.find(left) == kernel.find(right)


def test_substitution_shares_every_subterm_it_leaves_alone() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    untouched = kernel.eq(base.bool_ty, base.literal(True), base.literal(False))
    truth = base.literal(True)
    rows_before = len(kernel)

    output, fact = substitute(kernel, variable, truth, untouched)

    assert output == untouched
    assert len(kernel) == rows_before
    assert fact_view(fact) == ("syn", variable, truth, untouched, untouched)


def test_substitution_rebuilds_only_the_spine_that_moved() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    constant = base.literal(False)
    truth = base.literal(True)
    source = kernel.eq(base.bool_ty, variable, constant)

    output, fact = substitute(kernel, variable, truth, source)
    rows = Rows(kernel)

    assert output != source
    assert rows[output].tag == "tm.eq"
    assert rows[output].children == [truth, constant]
    assert fact_view(fact) == ("syn", variable, truth, source, output)


def test_substitution_visits_a_shared_subterm_once() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    shared = kernel.eq(base.bool_ty, variable, variable)
    source = kernel.eq(base.bool_ty, shared, shared)

    _, fact = substitute(kernel, variable, truth, source)

    assert fact.relation == "syn"
    # Two `tm.eq` levels and one variable: nine slots would mean the shared
    # child was proved twice.
    assert kernel.syn_fact_len() <= 6


@pytest.mark.parametrize(
    "build",
    [
        lambda base, variable: base.kernel.ty_exists(9, variable),
        lambda base, variable: base.kernel.model(9, variable),
        lambda base, variable: base.kernel.eq(base.bool_ty, variable, variable),
    ],
)
def test_substitution_enters_every_binding_and_non_binding_form(build) -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    source = build(base, variable)

    output, fact = substitute(kernel, variable, truth, source)
    rows = Rows(kernel)

    assert output != source
    assert rows[output].tag == rows[source].tag
    assert fact_view(fact) == ("syn", variable, truth, source, output)


def test_substitution_under_a_lambda_keeps_the_binder() -> None:
    base = basis()
    kernel = base.kernel
    replaced = base.var(1)
    binder = base.var(2)
    truth = base.literal(True)
    source = kernel.lam(binder, kernel.eq(base.bool_ty, binder, replaced))

    output, fact = substitute(kernel, replaced, truth, source)
    rows = Rows(kernel)

    assert rows[output].tag == "tm.lam"
    assert rows[output].children[0] == binder
    assert rows[rows[output].children[1]].children == [binder, truth]
    assert fact.var == replaced
    assert fact.val == truth


def test_beta_reduces_a_two_argument_application_step_by_step() -> None:
    base = basis()
    kernel = base.kernel
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function_binder = kernel.tm_fv(1, function_ty)
    argument_binder = base.var(2)
    twice = kernel.lam(
        function_binder,
        kernel.lam(
            argument_binder,
            kernel.app(function_binder, kernel.app(function_binder, argument_binder)),
        ),
    )
    function = kernel.tm_fv(3, function_ty)
    argument = base.var(4)

    outer_redex = kernel.app(twice, function)
    partial, first = beta(kernel, outer_redex)
    kernel.union_syn_fact(first)
    inner_redex = kernel.app(partial, argument)
    applied, second = beta(kernel, inner_redex)
    kernel.union_syn_fact(second)
    rows = Rows(kernel)

    assert first.relation == second.relation == "conv"
    assert rows[applied].tag == "tm.app"
    outer_function, inner = rows[applied].children
    assert outer_function == function
    assert rows[inner].children == [function, argument]
    assert kernel.equivalent(outer_redex, partial)
    assert kernel.equivalent(inner_redex, applied)


def test_beta_declines_anything_that_is_not_a_root_redex() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    opaque = kernel.tm_fv(1, function_ty)

    with pytest.raises(CannotProveError, match="not an application"):
        beta(kernel, truth)
    with pytest.raises(CannotProveError, match="not a tm.lam"):
        beta(kernel, kernel.app(opaque, truth))


def test_the_row_cache_picks_up_rows_created_after_it() -> None:
    base = basis()
    kernel = base.kernel
    rows = Rows(kernel)
    assert len(rows) == 2

    later = base.literal(True)
    assert rows[later].tag == "tm.bool"
    assert len(rows) == 3


def test_the_row_cache_still_reports_a_reference_that_does_not_exist() -> None:
    base = basis()
    rows = Rows(base.kernel)

    with pytest.raises(KeyError):
        rows[900]
