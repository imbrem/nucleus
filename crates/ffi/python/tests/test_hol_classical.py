"""The i32 CNF-to-DNF theorem surface is checked, nested, and transactional."""

import pytest
from covalence.logic.hol import Kernel


def fixture() -> tuple[Kernel, int, int, int, int]:
    kernel = Kernel()
    star = kernel.star()
    bool_ty = kernel.bool_ty(star)
    p_ref = kernel.tm_fv(1, bool_ty)
    q_ref = kernel.tm_fv(2, bool_ty)
    return kernel, bool_ty, kernel.lit(p_ref), kernel.lit(q_ref), p_ref


def test_literals_and_every_index_are_i32_checked_python_ints() -> None:
    kernel, _, p, _, p_ref = fixture()
    assert isinstance(p, int)
    assert p == -p_ref
    assert kernel.lit(p_ref, negated=True) == -p

    for malformed in (0, 2**31 - 1, -(2**31)):
        with pytest.raises(ValueError):
            kernel.identity(malformed)
    for outside_i32 in (2**31, -(2**31) - 1, 2**63, -(2**63) - 1):
        with pytest.raises(OverflowError):
            kernel.identity(outside_i32)
    for malformed in (0, -1):
        with pytest.raises(ValueError):
            kernel.theorem(malformed)
    for outside_i32 in (2**31, -(2**31) - 1, 2**63):
        with pytest.raises(OverflowError):
            kernel.theorem(outside_i32)


def test_nested_cnf_dnf_inspection_weakening_transfers_and_normalization() -> None:
    kernel, _, p, q, _ = fixture()
    theorem = kernel.identity(p)
    assert isinstance(theorem, int)
    assert kernel.theorem(theorem) == ([[p]], [[p]])

    kernel.weaken_matrix(theorem, [[q, p, q]], [[-q, p, -q]])
    assert kernel.theorem(theorem) == ([[p], [q, p, q]], [[p], [-q, p, -q]])
    kernel.move_cnf_right(theorem, 2)
    assert [-q, -p, -q] in kernel.theorem(theorem)[1]
    kernel.move_dnf_left(theorem, 1)
    before = kernel.theorem(theorem)
    with pytest.raises(ValueError):
        kernel.move_cnf_right(theorem, 0)
    with pytest.raises(OverflowError):
        kernel.move_dnf_left(theorem, 2**31)
    assert kernel.theorem(theorem) == before


def test_identity_cut_resolution_copy_remove_and_free_list_reuse() -> None:
    kernel, _, p, q, _ = fixture()
    left = kernel.identity(p)
    right = kernel.identity(p)
    assert kernel.theorem(kernel.cut(left, right, p)) == ([[p]], [[p]])

    negated = kernel.identity(-p)
    resolved = kernel.resolve(left, negated, p)
    assert kernel.theorem(resolved) == ([[p], [-p]], [])

    reusable = kernel.identity(q)
    assert kernel.remove_theorem(reusable)
    copied = kernel.copy_theorem(left)
    assert copied == reusable
    assert kernel.theorem(copied) == kernel.theorem(left)
    assert kernel.remove_theorem(copied)
    assert not kernel.remove_theorem(copied)
    with pytest.raises(ValueError):
        kernel.theorem(copied)
    # IDs are explicitly ephemeral: allocation reuses the removed slot.
    assert kernel.identity(q) == copied


def test_rejected_rules_are_atomic_and_do_not_consume_slots() -> None:
    kernel, _, p, q, _ = fixture()
    theorem = kernel.identity(p)
    before = kernel.theorem(theorem)
    with pytest.raises(ValueError):
        kernel.weaken(theorem, [q, 0], [])
    with pytest.raises(OverflowError):
        kernel.weaken_matrix(theorem, [[q], [2**31]], [])
    with pytest.raises(ValueError):
        kernel.not_left(theorem, q)
    with pytest.raises(ValueError):
        kernel.cut(theorem, theorem, q)
    assert kernel.theorem(theorem) == before
    assert kernel.identity(q) == theorem + 1


def test_constants_connective_rules_and_tree_normalization() -> None:
    kernel, bool_ty, p, q, p_ref = fixture()
    q_ref = abs(q)
    falsehood = kernel.lit(kernel.bool(bool_ty, False))
    truth = kernel.lit(kernel.bool(bool_ty, True))
    assert kernel.theorem(kernel.false_left(falsehood)) == ([[falsehood]], [])
    assert kernel.theorem(kernel.true_right(truth)) == ([], [[truth]])

    conjunction = kernel.lit(kernel.logical_and(p_ref, q_ref))
    disjunction = kernel.lit(kernel.logical_or(p_ref, q_ref))
    implication = kernel.lit(kernel.logical_imp(p_ref, q_ref))

    both_left = kernel.identity(p)
    kernel.weaken(both_left, [q], [])
    assert kernel.and_left(both_left, conjunction)
    assert kernel.and_right(kernel.identity(p), kernel.identity(q), conjunction)
    assert kernel.or_left(kernel.identity(p), kernel.identity(q), disjunction)
    both_right = kernel.identity(p)
    kernel.weaken(both_right, [], [q])
    assert kernel.or_right(both_right, disjunction)
    assert kernel.imp_left(kernel.identity(p), kernel.identity(q), implication)
    implication_right = kernel.identity(q)
    kernel.weaken(implication_right, [p], [])
    assert kernel.imp_right(implication_right, implication)

    conjunction_identity = kernel.identity(conjunction)
    flat_left = kernel.flatten_premise(conjunction_identity, conjunction)
    folded_left = kernel.fold_premise(flat_left, conjunction)
    assert kernel.theorem(folded_left) == kernel.theorem(conjunction_identity)
    disjunction_identity = kernel.identity(disjunction)
    flat_right = kernel.flatten_conclusion(disjunction_identity, disjunction)
    folded_right = kernel.fold_conclusion(flat_right, disjunction)
    assert kernel.theorem(folded_right) == kernel.theorem(disjunction_identity)


def test_negation_and_expansion_have_no_unchecked_admission_path() -> None:
    kernel, _, p, _, p_ref = fixture()
    theorem = kernel.identity(p)
    kernel.not_left(theorem, p)
    assert kernel.theorem(theorem) == ([[p], [-p]], [])
    theorem = kernel.identity(p)
    kernel.not_right(theorem, p)
    assert kernel.theorem(theorem) == ([], [[p], [-p]])

    not_p = kernel.lit(kernel.logical_not(p_ref))
    expanded = kernel.expand_conclusion(kernel.identity(not_p), not_p)
    assert kernel.theorem(expanded)[1] == [[-p]]
    with pytest.raises(ValueError):
        kernel.identity(kernel.lit(999_999))


def test_standard_hol_rules_preserve_i32_ids_and_checked_contexts() -> None:
    kernel, bool_ty, p, q, p_ref = fixture()
    q_ref = abs(q)
    equality = kernel.eq(bool_ty, p_ref, q_ref)
    equality_assumption = kernel.identity(kernel.lit(equality))

    function_ty = kernel.ty_arr(bool_ty, bool_ty)
    function = kernel.tm_fv(20, function_ty)
    left, right, applied_equality, applied_theorem = kernel.ap_term(
        equality_assumption, function
    )
    assert all(
        isinstance(value, int) and value > 0
        for value in (left, right, applied_equality)
    )
    assert kernel.theorem(applied_theorem) == (
        [[kernel.lit(equality)]],
        [[kernel.lit(applied_equality)]],
    )

    rewritten = kernel.eq_mp(equality_assumption, kernel.identity(p))
    assert kernel.theorem(rewritten) == ([[kernel.lit(equality)], [p]], [[q]])

    binder = kernel.tm_fv(21, bool_ty)
    truth = kernel.bool(bool_ty, True)
    universal, generalized = kernel.forall_intro(
        kernel.true_right(kernel.lit(truth)), binder
    )
    assert kernel.theorem(generalized) == ([], [[kernel.lit(universal)]])
    with pytest.raises(ValueError):
        kernel.forall_intro(generalized, bool_ty)

    predicate = kernel.tm_fv(22, function_ty)
    application = kernel.app(predicate, p_ref)
    witness, proposition, selected = kernel.choice_intro(
        kernel.identity(kernel.lit(application))
    )
    assert all(
        isinstance(value, int) and value > 0
        for value in (witness, proposition, selected)
    )
    assert kernel.theorem(selected) == (
        [[kernel.lit(application)]],
        [[kernel.lit(proposition)]],
    )
