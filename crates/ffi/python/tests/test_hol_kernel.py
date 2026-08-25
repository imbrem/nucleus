"""The checked kernel starts empty and only grows through checked rules.

A `Kernel` shares the arena representation but nothing else with `Arena`: its
constructors validate tags, categories, and classifiers on every call, and it
records the classifier it derived rather than the one a caller claimed. These
tests drive the constructor surface, every rejection it can produce, and the
boundary between the checked kernel and the raw arena it can hand out.
"""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import (
    Arena,
    Kernel,
    Kind,
    Link,
    SynFact,
    Tm,
    Ty,
    load_standard_proof,
)
from hol_support import Rows, basis, beta, prove_congruence, unify


def test_standard_proof_loader_rejects_non_components() -> None:
    with pytest.raises(RuntimeError, match="proof component failed"):
        load_standard_proof(b"not a WebAssembly component")


MISSING = "does not name a kernel row"
WRONG_CATEGORY = "was required"
ONE_BASED = "one-based"


def test_a_new_kernel_is_empty_and_addresses_the_empty_arena() -> None:
    kernel = Kernel()

    assert len(kernel) == 0
    assert kernel.arena.definitions == []
    assert kernel.addr() == Arena().addr()
    assert kernel.syn_fact_len() == 0


def test_constructors_record_the_classifier_they_derived() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(1)
    truth = base.literal(True)
    identity = kernel.lam(variable, variable)
    applied = kernel.app(identity, truth)
    equation = kernel.eq(base.bool_ty, applied, truth)

    assert kernel.category(base.star) == "kind"
    assert kernel.category(base.bool_ty) == "ty"
    assert kernel.category(truth) == "tm"
    assert kernel.classifier(base.bool_ty) == base.star
    assert kernel.classifier(variable) == base.bool_ty
    assert kernel.classifier(truth) == base.bool_ty
    assert kernel.classifier(applied) == base.bool_ty
    assert kernel.classifier(equation) == base.bool_ty
    assert kernel.arena.sort[base.star - 1] is None
    assert kernel.arena.sort[base.bool_ty - 1] == base.star
    assert kernel.arena.sort[truth - 1] == base.bool_ty
    # `lam` derives and appends its own arrow type rather than trusting one.
    arrow = kernel.classifier(identity)
    assert kernel.arena.definition(arrow).tag == "ty.arr"
    assert kernel.arena.definition(arrow).children == [base.bool_ty, base.bool_ty]


def test_higher_kinded_rows_carry_arrow_kinds() -> None:
    base = basis()
    kernel = base.kernel
    arrow = kernel.kind_arr(base.star, base.star)
    family = kernel.ty_fv(1, arrow)
    argument = kernel.ty_fv(2, base.star)
    applied = kernel.ty_app(family, argument)
    abstracted = kernel.ty_lam(argument, applied)

    assert kernel.classifier(family) == arrow
    assert kernel.classifier(applied) == base.star
    assert kernel.arena.definition(kernel.classifier(abstracted)).tag == "kind.arr"


def test_model_is_a_type_and_ty_exists_is_a_term() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    model = kernel.model(9, truth)

    assert kernel.category(model) == "ty"
    assert kernel.arena.sort[model - 1] == base.star
    assert kernel.category(kernel.ty_exists(9, truth)) == "tm"


def test_kinds_are_compared_syntactically_and_types_by_class() -> None:
    """`ty_app` wants the exact domain reference; `app` accepts the class."""
    base = basis()
    kernel = base.kernel
    star = base.star
    other_star = kernel.star()
    arrow = kernel.kind_arr(star, star)
    family = kernel.ty_fv(1, arrow)
    same_kind = kernel.ty_fv(2, star)
    other_kind = kernel.ty_fv(3, other_star)

    assert kernel.ty_app(family, same_kind)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.ty_app(family, other_kind)

    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function = kernel.tm_fv(4, function_ty)
    duplicate_bool = kernel.bool_ty(star)
    argument = kernel.tm_fv(5, duplicate_bool)
    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.app(function, argument)

    unify(kernel, base.bool_ty, duplicate_bool)
    assert kernel.app(function, argument)


def test_a_bool_type_is_anything_in_a_class_holding_ty_bool() -> None:
    """The check is on the equality class, not on the row's own tag."""
    base = basis()
    kernel = base.kernel
    parameter = kernel.ty_fv(1, base.star)
    family = kernel.ty_lam(parameter, parameter)
    applied = kernel.ty_app(family, base.bool_ty)

    with pytest.raises(ValueError, match="a type class containing ty.bool"):
        kernel.bool(applied, True)

    _, contraction = beta(kernel, applied)
    kernel.union_syn_fact(contraction)

    assert kernel.equivalent(applied, base.bool_ty)
    assert kernel.bool(applied, True)
    assert kernel.tm_fv(2, applied)


def test_reflexivity_alone_never_widens_a_class() -> None:
    base = basis()
    kernel = base.kernel
    alias = kernel.ty_fv(1, base.star)

    kernel.union_syn_fact(prove_congruence(kernel, alias, alias))

    assert not kernel.equivalent(alias, base.bool_ty)
    with pytest.raises(ValueError, match="a type class containing ty.bool"):
        kernel.bool(alias, True)


@pytest.mark.parametrize(
    ("build", "message"),
    [
        (lambda base: base.kernel.category(900), MISSING),
        (lambda base: base.kernel.classifier(base.star), "has no sort member"),
        (lambda base: base.kernel.bool_ty(base.bool_ty), "kind.star was required"),
        (lambda base: base.kernel.ty_arr(base.star, base.star), WRONG_CATEGORY),
        (lambda base: base.kernel.tm_fv(1, base.star), WRONG_CATEGORY),
        (lambda base: base.kernel.app(base.star, base.star), WRONG_CATEGORY),
        (lambda base: base.kernel.lam(base.bool_ty, base.bool_ty), "tm.fv"),
        (lambda base: base.kernel.ty_lam(base.bool_ty, base.bool_ty), "ty.fv"),
        (lambda base: base.kernel.bool(base.star, True), WRONG_CATEGORY),
        (lambda base: base.kernel.eps(base.bool_ty, base.literal(True)), "ty.arr"),
        (lambda base: base.kernel.ty_app(base.bool_ty, base.bool_ty), "kind.arr"),
        (lambda base: base.kernel.model(1, base.bool_ty), WRONG_CATEGORY),
        (lambda base: base.kernel.ty_exists(1, base.bool_ty), WRONG_CATEGORY),
        (lambda base: base.kernel.add_context(base.star), WRONG_CATEGORY),
    ],
)
def test_every_constructor_rejects_the_wrong_row(build, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        build(basis())


def test_equality_operands_must_share_a_type_class() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    function_ty = kernel.ty_arr(base.bool_ty, base.bool_ty)
    function = kernel.tm_fv(1, function_ty)

    with pytest.raises(ValueError, match="is not equal to expected"):
        kernel.eq(base.bool_ty, truth, function)
    assert kernel.eq(base.bool_ty, truth, truth)


@pytest.mark.parametrize(
    "build",
    [
        lambda kernel: kernel.category(0),
        lambda kernel: kernel.classifier(0),
        lambda kernel: kernel.find(0),
        lambda kernel: kernel.find_mut(0),
        lambda kernel: kernel.equivalent(0, 1),
        lambda kernel: kernel.kind(0),
        lambda kernel: kernel.ty(0),
        lambda kernel: kernel.tm(0),
        lambda kernel: kernel.kind_arr(0, 1),
        lambda kernel: kernel.bool_ty(0),
        lambda kernel: kernel.add_context(0),
        lambda kernel: kernel.syn_fact(0),
        lambda kernel: kernel.syn_refl("syn", 0),
    ],
)
def test_zero_is_never_a_kernel_reference(build) -> None:
    with pytest.raises(ValueError, match=ONE_BASED):
        build(Kernel())


def test_only_the_infinity_capability_is_available() -> None:
    kernel = Kernel()

    kernel.add_axiom("ax.inf")
    assert kernel.arena.axioms == ["ax.inf"]
    for name in ("ax.choice", "ax.inf ", "", "AX.INF"):
        with pytest.raises(ValueError, match="unsupported axiom capability"):
            kernel.add_axiom(name)
    assert kernel.arena.axioms == ["ax.inf"]


def test_the_context_only_admits_boolean_terms() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    kernel.add_context(truth)
    kernel.add_context(truth)

    assert kernel.arena.context == [truth]
    with pytest.raises(ValueError, match=WRONG_CATEGORY):
        kernel.add_context(base.bool_ty)


def test_the_arena_a_kernel_hands_out_is_detached() -> None:
    """Editing the copy cannot smuggle an unchecked row into the kernel."""
    base = basis()
    kernel = base.kernel

    borrowed = kernel.arena
    borrowed.bool(True)
    borrowed.add_axiom("ax.choice")
    borrowed.add_context(9000)

    assert kernel.arena is not borrowed
    assert len(kernel) == len(kernel.arena) == 2
    assert kernel.arena.axioms == []
    assert kernel.arena.context == []
    assert kernel.addr() == kernel.arena.addr()
    assert kernel.addr() != borrowed.addr()


def test_the_address_moves_with_every_appended_row() -> None:
    kernel = Kernel()
    seen = {kernel.addr()}

    star = kernel.star()
    seen.add(kernel.addr())
    kernel.bool_ty(star)
    seen.add(kernel.addr())

    assert len(seen) == 3
    assert kernel.addr() == kernel.arena.addr()


def test_imports_are_recorded_without_being_believed() -> None:
    nonsense = Arena()
    nonsense.kind_arr(900, 901)
    kernel = Kernel()

    literal = kernel.import_literal(nonsense)
    link = kernel.import_link(Link(O256.hash(b"unresolved")))

    assert (literal, link) == (1, 2)
    assert kernel.arena.imports[0].addr() == nonsense.addr()
    assert kernel.arena.imports[1].blake3 == O256.hash(b"unresolved")
    # An import is data. It contributes no rows and no premises on its own.
    assert len(kernel) == 0
    assert kernel.arena.amb_ctx == []


def test_handles_name_a_row_of_the_category_that_minted_them() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)

    assert isinstance(kernel.kind(base.star), Kind)
    assert isinstance(kernel.ty(base.bool_ty), Ty)
    assert isinstance(kernel.tm(truth), Tm)
    assert kernel.kind(base.star).reference == base.star
    assert kernel.ty(base.bool_ty).reference == base.bool_ty
    assert kernel.tm(truth).reference == truth

    with pytest.raises(ValueError, match="not a kind"):
        kernel.kind(base.bool_ty)
    with pytest.raises(ValueError, match="not a type"):
        kernel.ty(base.star)
    with pytest.raises(ValueError, match="not a term"):
        kernel.tm(base.star)
    with pytest.raises(ValueError, match=MISSING):
        kernel.kind(900)


@pytest.mark.parametrize("opaque", [Kind, Ty, Tm, SynFact])
def test_opaque_handles_cannot_be_forged(opaque) -> None:
    with pytest.raises(TypeError):
        opaque()


def test_handles_are_frozen_views_of_a_reference() -> None:
    base = basis()
    handle = base.kernel.ty(base.bool_ty)

    with pytest.raises(AttributeError):
        handle.reference = 1


def test_equality_starts_discrete_and_is_reflexive() -> None:
    base = basis()
    kernel = base.kernel
    truth = base.literal(True)
    falsehood = base.literal(False)

    for reference in (base.star, base.bool_ty, truth, falsehood):
        assert kernel.find(reference) == reference
        assert kernel.find_mut(reference) == reference
        assert kernel.equivalent(reference, reference)

    assert not kernel.equivalent(truth, falsehood)
    # Rows of different categories are never equivalent, and asking is not an
    # error the way a missing row is.
    assert not kernel.equivalent(base.star, base.bool_ty)
    with pytest.raises(ValueError, match=MISSING):
        kernel.equivalent(truth, 900)


def test_union_picks_the_smaller_reference_as_representative() -> None:
    base = basis()
    kernel = base.kernel
    first = base.literal(True)
    second = base.literal(True)
    third = base.literal(True)

    unify(kernel, second, third)
    unify(kernel, first, third)

    assert kernel.find(first) == first
    assert kernel.find(second) == first
    assert kernel.find(third) == first
    assert kernel.equivalent(first, third)
    assert kernel.find_mut(third) == first
    # Compression rewrites the stored parent without changing the class.
    assert kernel.arena.eq[third - 1] == first


def test_the_hol_kernel_is_the_only_production_proof_kernel() -> None:
    """LRAT parsing no longer exposes a standalone proof authority."""
    from covalence.logic import lrat

    assert Kernel.__module__ == "covalence.logic.hol"
    assert not hasattr(lrat, "Kernel")


def test_dense_columns_expose_the_checked_members() -> None:
    base = basis()
    kernel = base.kernel
    variable = base.var(7)
    rows = Rows(kernel)

    assert rows[variable].tag == "tm.fv"
    assert rows[variable].name == 7
    assert rows[variable].children == [base.bool_ty]
    assert kernel.arena.sort[variable - 1] == base.bool_ty
    assert kernel.arena.sort[base.star - 1] is None
