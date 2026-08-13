"""The Python LRAT API delegates validation and state to the Rust kernel."""

import pytest
from covalence.logic.lrat import Kernel, LratError, RatGroup
from covalence.logic.sat import Clause, Formula, Literal


def test_rup_refutes_a_unit_contradiction() -> None:
    kernel = Kernel(Formula([Clause([1]), Clause([-1])]))

    assert kernel.high_water == 2
    assert not kernel.refuted
    kernel.learn_rup(3, Clause([]), [1, 2])

    assert kernel.refuted
    assert kernel.high_water == 3
    assert kernel.clause(3) == []
    assert kernel.clause(99) is None


def test_rejection_is_transactional() -> None:
    kernel = Kernel(Formula([Clause([1]), Clause([-1])]))

    with pytest.raises(LratError, match="UnknownClause"):
        kernel.learn_rup(3, Clause([]), [99])

    assert kernel.high_water == 2
    assert not kernel.refuted
    assert kernel.clause(3) is None


def test_forget_preserves_the_high_water_mark() -> None:
    kernel = Kernel(Formula([Clause([1]), Clause([-1])]))
    kernel.learn_rup(3, Clause([1]), [1])
    kernel.forget([3])

    assert kernel.clause(3) is None
    assert kernel.high_water == 3
    with pytest.raises(LratError, match="NonFreshId"):
        kernel.learn_rup(3, Clause([1]), [1])


def test_rat_groups_are_explicit_values() -> None:
    group = RatGroup(7, [1, 2])

    assert group.opposing_clause_id == 7
    assert group.resolvent_rup_hints == [1, 2]
    assert repr(group) == "RatGroup(7, [1, 2])"


def test_invalid_literals_are_rejected() -> None:
    with pytest.raises(LratError, match="InvalidLiteral"):
        Clause([0])
