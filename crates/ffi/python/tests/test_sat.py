"""The Python SAT API preserves the Rust CNF value model."""

import pytest
from covalence.logic.sat import Clause, CnfError, Formula, Literal


def test_literals_are_nonzero_signed_variables() -> None:
    literal = Literal(-7)

    assert literal.value == -7
    assert literal.variable == 7
    assert int(-literal) == 7
    assert literal == Literal(-7)
    assert literal < Literal(1)
    assert hash(literal) == hash(Literal(-7))
    assert repr(literal) == "Literal(-7)"
    with pytest.raises(CnfError):
        Literal(0)


def test_clauses_and_formulas_are_typed_values() -> None:
    first = Clause([1, -2])
    empty = Clause([])
    formula = Formula([first, empty])

    assert first.literals == [1, -2]
    assert first == Clause([1, -2])
    assert empty < first
    assert hash(first) == hash(Clause([1, -2]))
    assert repr(first) == "Clause([1, -2])"
    assert len(formula) == 2
    assert formula == Formula([Clause([1, -2]), Clause([])])
    assert Formula([empty]) < formula
    assert hash(formula) == hash(Formula([Clause([1, -2]), Clause([])]))
    assert formula.max_variable == 2
    assert [clause.literals for clause in formula.clauses] == [[1, -2], []]
