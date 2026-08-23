"""The checked kernel only ever grows through checked rules.

A `Kernel` starts empty and has no way to absorb a row it did not build, so
every test here starts from nothing and works forward. What is being pinned is
the shape of the checking: which operands each rule demands, what classifier it
records, and which malformed calls it refuses.
"""

import doctest
import pathlib

import pytest
from covalence.logic.hol import Arena, Kernel, Kind, Link, SynFact, Tm, Ty
from hol_support import (
    KERNEL_REFERENCE_CALLS,
    SUPPORTED_AXIOM,
    assert_kernel_invariants,
    bool_kernel,
    call_names,
    definitions_by_reference,
    merge_congruent,
)


def test_a_new_kernel_is_the_empty_arena() -> None:
    kernel = Kernel()
    assert len(kernel) == 0
    assert kernel.syn_fact_len() == 0
    assert kernel.addr() == Arena().addr()
    assert kernel.arena.to_cbor() == Arena().to_cbor()
    assert_kernel_invariants(kernel)


def test_rows_are_appended_not_shared() -> None:
    """No hash-consing: equal syntax is equal only once something proves it."""
    kernel = Kernel()
    first = kernel.star()
    second = kernel.star()
    assert first != second
    assert not kernel.equivalent(first, second)

    left = kernel.bool_ty(first)
    right = kernel.bool_ty(second)
    assert not kernel.equivalent(left, right)
    # Both are still `ty.bool`, so both work wherever a Boolean type is wanted.
    assert kernel.category(kernel.bool(left, True)) == "tm"
    assert kernel.category(kernel.bool(right, False)) == "tm"
    assert_kernel_invariants(kernel)


def test_each_constructor_records_the_classifier_it_promises() -> None:
    kernel, star, bool_ty = bool_kernel()
    arrow_kind = kernel.kind_arr(star, star)
    family = kernel.ty_fv(1, arrow_kind)
    argument = kernel.ty_fv(2, star)
    applied = kernel.ty_app(family, argument)
    abstracted = kernel.ty_lam(argument, applied)
    function_ty = kernel.ty_arr(bool_ty, bool_ty)
    variable = kernel.tm_fv(3, bool_ty)
    truth = kernel.bool(bool_ty, True)
    identity = kernel.lam(variable, variable)
    applied_term = kernel.app(identity, truth)
    equation = kernel.eq(bool_ty, truth, applied_term)
    predicate = kernel.tm_fv(4, function_ty)
    choice = kernel.eps(bool_ty, predicate)
    model = kernel.model(5, truth)
    exists = kernel.ty_exists(6, truth)

    rows = definitions_by_reference(kernel.arena)
    assert kernel.classifier(bool_ty) == star
    assert kernel.classifier(family) == arrow_kind
    assert kernel.classifier(applied) == star
    assert rows[kernel.classifier(abstracted)].tag == "kind.arr"
    assert kernel.classifier(variable) == bool_ty
    assert kernel.classifier(truth) == bool_ty
    assert rows[kernel.classifier(identity)].tag == "ty.arr"
    assert kernel.classifier(applied_term) == bool_ty
    assert kernel.classifier(equation) == bool_ty
    assert kernel.classifier(choice) == bool_ty
    assert kernel.classifier(model) == star
    assert kernel.classifier(exists) == bool_ty

    assert kernel.category(star) == "kind"
    assert kernel.category(bool_ty) == "ty"
    assert kernel.category(model) == "ty"
    assert kernel.category(exists) == "tm"
    assert rows[model].tag == "ty.model"
    assert rows[exists].tag == "tm.ty_exists"
    assert_kernel_invariants(kernel)


def test_abstraction_allocates_the_classifier_it_needs() -> None:
    """`lam` and `ty_lam` append the arrow row rather than demanding one."""
    kernel, star, bool_ty = bool_kernel()
    before = len(kernel)
    variable = kernel.tm_fv(1, bool_ty)
    identity = kernel.lam(variable, variable)
    # The variable row, the arrow type it induces, and the lambda itself.
    assert len(kernel) == before + 3
    assert kernel.classifier(identity) == identity - 1
    assert kernel.arena.definition(kernel.classifier(identity)).children == [
        bool_ty,
        bool_ty,
    ]


def test_the_kernel_arena_is_a_detached_snapshot() -> None:
    """Reading the arena hands out a copy, so it cannot be edited back in."""
    kernel, star, bool_ty = bool_kernel()
    snapshot = kernel.arena
    assert snapshot is not kernel.arena

    snapshot.bool_ty()
    snapshot.add_axiom("ax.forged")
    snapshot.add_context(1)
    assert len(kernel) == 2
    assert kernel.arena.axioms == []
    assert kernel.arena.context == []
    assert_kernel_invariants(kernel)


def test_the_kernel_address_is_its_arena_address() -> None:
    kernel, star, bool_ty = bool_kernel()
    assert kernel.addr() == kernel.arena.addr()
    before = kernel.addr()
    kernel.bool(bool_ty, True)
    assert kernel.addr() != before
    assert kernel.addr() == kernel.arena.addr()


@pytest.mark.parametrize(
    ("name", "call"),
    KERNEL_REFERENCE_CALLS,
    ids=call_names(KERNEL_REFERENCE_CALLS),
)
def test_every_kernel_index_rejects_zero(name: str, call) -> None:
    kernel, star, bool_ty = bool_kernel()
    with pytest.raises(ValueError, match="one-based"):
        call(kernel)


@pytest.mark.parametrize(
    ("name", "call"),
    [
        ("category", lambda kernel: kernel.category(99)),
        ("classifier", lambda kernel: kernel.classifier(99)),
        ("find", lambda kernel: kernel.find(99)),
        ("find_mut", lambda kernel: kernel.find_mut(99)),
        ("equivalent", lambda kernel: kernel.equivalent(99, 1)),
        ("kind", lambda kernel: kernel.kind(99)),
        ("ty", lambda kernel: kernel.ty(99)),
        ("tm", lambda kernel: kernel.tm(99)),
        ("kind_arr", lambda kernel: kernel.kind_arr(99, 1)),
        ("bool_ty", lambda kernel: kernel.bool_ty(99)),
        ("bool", lambda kernel: kernel.bool(99, True)),
        ("app", lambda kernel: kernel.app(99, 1)),
        ("add_context", lambda kernel: kernel.add_context(99)),
        ("syn_refl", lambda kernel: kernel.syn_refl("syn", 99)),
    ],
    ids=lambda value: value if isinstance(value, str) else "",
)
def test_references_past_the_end_are_rejected(name: str, call) -> None:
    kernel, star, bool_ty = bool_kernel()
    with pytest.raises(ValueError, match="does not name a kernel row"):
        call(kernel)


def test_kind_rules_demand_kinds() -> None:
    kernel, star, bool_ty = bool_kernel()
    with pytest.raises(ValueError, match="declares Ty, but Kind was required"):
        kernel.kind_arr(bool_ty, star)
    with pytest.raises(ValueError, match="declares Ty, but Kind was required"):
        kernel.kind_arr(star, bool_ty)
    with pytest.raises(ValueError, match="kind.star was required"):
        kernel.bool_ty(bool_ty)
    with pytest.raises(ValueError, match="kind.star was required"):
        kernel.bool_ty(kernel.kind_arr(star, star))


def test_type_rules_demand_well_kinded_types() -> None:
    kernel, star, bool_ty = bool_kernel()
    arrow_kind = kernel.kind_arr(star, star)
    family = kernel.ty_fv(1, arrow_kind)

    with pytest.raises(ValueError, match="declares Kind, but Ty was required"):
        kernel.ty_arr(star, bool_ty)
    # A type family has an arrow kind, so it is not a type of kind `star`.
    with pytest.raises(ValueError, match="kind.star was required"):
        kernel.ty_arr(family, bool_ty)
    with pytest.raises(ValueError, match="kind.arr was required"):
        kernel.ty_app(bool_ty, bool_ty)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.ty_app(family, kernel.ty_fv(2, arrow_kind))
    with pytest.raises(ValueError, match="ty.fv was required"):
        kernel.ty_lam(bool_ty, bool_ty)


def test_term_rules_demand_well_typed_terms() -> None:
    kernel, star, bool_ty = bool_kernel()
    function_ty = kernel.ty_arr(bool_ty, bool_ty)
    function = kernel.tm_fv(1, function_ty)
    truth = kernel.bool(bool_ty, True)

    with pytest.raises(ValueError, match="declares Kind, but Ty was required"):
        kernel.tm_fv(2, star)
    family = kernel.ty_fv(3, kernel.kind_arr(star, star))
    with pytest.raises(ValueError, match="kind.star was required"):
        kernel.tm_fv(4, family)
    with pytest.raises(ValueError, match="a type class containing ty.arr"):
        kernel.app(truth, truth)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.app(function, function)
    with pytest.raises(ValueError, match="tm.fv was required"):
        kernel.lam(truth, truth)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.lam(kernel.tm_fv(3, bool_ty), bool_ty)
    with pytest.raises(ValueError, match="a type class containing ty.bool"):
        kernel.bool(function_ty, True)
    assert kernel.category(kernel.app(function, truth)) == "tm"


def test_equality_demands_one_type_class() -> None:
    kernel, star, bool_ty = bool_kernel()
    function_ty = kernel.ty_arr(bool_ty, bool_ty)
    truth = kernel.bool(bool_ty, True)
    function = kernel.tm_fv(1, function_ty)

    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.eq(bool_ty, truth, function)
    with pytest.raises(ValueError, match="a type class containing ty.bool"):
        kernel.eq(function_ty, truth, truth)
    assert kernel.category(kernel.eq(bool_ty, truth, truth)) == "tm"


def test_choice_demands_a_predicate_over_its_type() -> None:
    kernel, star, bool_ty = bool_kernel()
    predicate_ty = kernel.ty_arr(bool_ty, bool_ty)
    predicate = kernel.tm_fv(1, predicate_ty)
    wrong_ty = kernel.ty_arr(bool_ty, predicate_ty)
    wrong = kernel.tm_fv(2, wrong_ty)

    assert kernel.classifier(kernel.eps(bool_ty, predicate)) == bool_ty
    with pytest.raises(ValueError, match="a type class containing ty.bool"):
        kernel.eps(bool_ty, wrong)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.eps(predicate_ty, predicate)


def test_propositional_binders_demand_boolean_predicates() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.model(1, bool_ty)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.ty_exists(1, bool_ty)
    assert kernel.category(kernel.model(1, truth)) == "ty"
    assert kernel.category(kernel.ty_exists(1, truth)) == "tm"


def test_context_takes_boolean_terms_only() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    with pytest.raises(ValueError, match="declares Kind, but Tm was required"):
        kernel.add_context(star)
    with pytest.raises(ValueError, match="declares Ty, but Tm was required"):
        kernel.add_context(bool_ty)

    kernel.add_context(truth)
    kernel.add_context(truth)
    assert kernel.arena.context == [truth]
    assert_kernel_invariants(kernel)


def test_only_the_infinity_capability_is_supported() -> None:
    kernel, star, bool_ty = bool_kernel()
    for name in ("", "ax.choice", "AX.INF", "ax.inf "):
        with pytest.raises(ValueError, match="unsupported axiom capability"):
            kernel.add_axiom(name)
    assert kernel.arena.axioms == []

    kernel.add_axiom(SUPPORTED_AXIOM)
    kernel.add_axiom(SUPPORTED_AXIOM)
    assert kernel.arena.axioms == [SUPPORTED_AXIOM]
    assert_kernel_invariants(kernel)


def test_imports_are_recorded_without_being_trusted() -> None:
    """A kernel may name an import; nothing about it is checked here."""
    nonsense = Arena()
    nonsense.kind_arr(9, 9)
    nonsense.add_axiom("ax.not.real")

    kernel, star, bool_ty = bool_kernel()
    literal = kernel.import_literal(nonsense)
    link = kernel.import_link(Link(nonsense.addr()))
    assert (literal, link) == (1, 2)

    entries = kernel.arena.imports
    assert isinstance(entries[0], Arena)
    assert entries[0].addr() == nonsense.addr()
    assert entries[1].blake3 == nonsense.addr()
    # Importing adds no rows and no premises of its own.
    assert len(kernel) == 2
    assert kernel.arena.assumptions == []
    assert_kernel_invariants(kernel)


def test_equality_classes_are_rooted_at_their_smallest_member() -> None:
    kernel, star, bool_ty = bool_kernel()
    first = kernel.bool(bool_ty, True)
    second = kernel.bool(bool_ty, True)
    third = kernel.bool(bool_ty, True)
    assert kernel.find(first) == first
    assert not kernel.equivalent(first, second)

    merge_congruent(kernel, second, third)
    merge_congruent(kernel, first, second)
    for reference in (first, second, third):
        assert kernel.find(reference) == first
    assert kernel.equivalent(first, third)
    assert_kernel_invariants(kernel)


def test_finding_compresses_only_when_asked() -> None:
    kernel, star, bool_ty = bool_kernel()
    first = kernel.bool(bool_ty, True)
    second = kernel.bool(bool_ty, True)
    third = kernel.bool(bool_ty, True)
    merge_congruent(kernel, first, second)
    merge_congruent(kernel, second, third)

    parents = {row.reference: row.equal for row in kernel.arena.definitions}
    assert kernel.find(third) == first
    assert {row.reference: row.equal for row in kernel.arena.definitions} == parents

    assert kernel.find_mut(third) == first
    assert kernel.arena.definition(third).equal == first
    assert kernel.find(third) == first
    assert_kernel_invariants(kernel)


def test_equivalence_across_categories_is_false_not_an_error() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)
    assert kernel.equivalent(star, bool_ty) is False
    assert kernel.equivalent(bool_ty, truth) is False
    assert kernel.equivalent(star, star) is True


def test_opaque_handles_check_the_category_they_claim() -> None:
    kernel, star, bool_ty = bool_kernel()
    truth = kernel.bool(bool_ty, True)

    assert isinstance(kernel.kind(star), Kind)
    assert isinstance(kernel.ty(bool_ty), Ty)
    assert isinstance(kernel.tm(truth), Tm)
    assert kernel.kind(star).reference == star
    assert kernel.ty(bool_ty).reference == bool_ty
    assert kernel.tm(truth).reference == truth

    with pytest.raises(ValueError, match="not a kind"):
        kernel.kind(bool_ty)
    with pytest.raises(ValueError, match="not a type"):
        kernel.ty(star)
    with pytest.raises(ValueError, match="not a term"):
        kernel.tm(bool_ty)


def test_handles_cannot_be_forged_by_construction() -> None:
    for opaque in (Kind, Ty, Tm, SynFact):
        with pytest.raises(TypeError):
            opaque()
    with pytest.raises(TypeError):
        Kind.__new__(Kind)


def test_handles_carry_no_value_identity() -> None:
    """They compare by object identity; `reference` is the comparable part."""
    kernel, star, bool_ty = bool_kernel()
    first = kernel.kind(star)
    second = kernel.kind(star)
    assert first is not second
    assert first != second
    assert first.reference == second.reference
    with pytest.raises(AttributeError):
        first.reference = 2  # type: ignore[misc]


def test_a_full_construction_stays_internally_consistent() -> None:
    """One long session, then every invariant at once."""
    kernel, star, bool_ty = bool_kernel()
    arrow_kind = kernel.kind_arr(star, star)
    family = kernel.ty_fv(1, arrow_kind)
    argument = kernel.ty_fv(2, star)
    kernel.ty_lam(argument, kernel.ty_app(family, argument))

    variable = kernel.tm_fv(3, bool_ty)
    identity = kernel.lam(variable, variable)
    truth = kernel.bool(bool_ty, True)
    falsity = kernel.bool(bool_ty, False)
    applied = kernel.app(identity, truth)
    kernel.add_context(kernel.eq(bool_ty, applied, truth))
    kernel.add_context(kernel.eq(bool_ty, falsity, falsity))
    kernel.add_axiom(SUPPORTED_AXIOM)
    kernel.model(4, truth)
    kernel.ty_exists(5, truth)
    kernel.eps(bool_ty, kernel.tm_fv(6, kernel.classifier(identity)))

    assert_kernel_invariants(kernel)
    assert len(kernel.arena.context) == 2
    assert Arena.from_cbor(kernel.arena.to_cbor()).addr() == kernel.addr()


def test_the_documented_example_runs() -> None:
    """The README's `covalence.logic.hol` block is executable, not prose."""
    readme = pathlib.Path(__file__).resolve().parent.parent / "README.md"
    blocks = [
        block.split("```", 1)[0]
        for block in readme.read_text().split("```python\n")[1:]
        if "covalence.logic.hol" in block.split("```", 1)[0]
    ]
    assert len(blocks) == 1, "the README documents exactly one HOL example"

    example = doctest.DocTestParser().get_doctest(blocks[0], {}, "README", None, 0)
    assert example.examples, "the HOL example has no runnable lines"
    results = doctest.DocTestRunner(optionflags=doctest.ELLIPSIS).run(
        example, out=lambda text: None
    )
    assert results.failed == 0
    assert results.attempted == len(example.examples)
