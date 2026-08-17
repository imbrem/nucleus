"""General decision diagrams and canonical BDDs."""

import operator

import pytest
from covalence.logic.bdd import BddError, BddManager, Diagram
from covalence.logic.sat import Clause, Formula


def test_general_diagrams_may_be_noncanonical() -> None:
    false = Diagram.constant(False)
    true = Diagram.constant(True)
    x = Diagram.branch(1, false, true)
    redundant_and_unordered = Diagram.branch(2, x, x)

    assert redundant_and_unordered.kind == "branch"
    assert redundant_and_unordered.variable == 2
    assert redundant_and_unordered.evaluate({1: True, 2: False})

    manager = BddManager()
    assert manager.reduce(redundant_and_unordered) == manager.variable(1)


def test_canonical_boolean_operations_and_evaluation() -> None:
    manager = BddManager()
    x = manager.variable(1)
    y = manager.variable(2)
    conjunction = x & y

    assert conjunction == y & x
    assert conjunction.variables == [1, 2]
    assert conjunction.evaluate({1: True, 2: True})
    assert not conjunction.evaluate({1: True, 2: False})
    assert (x | ~x).is_true
    assert (x ^ x).is_false
    assert x.implies(y).evaluate({1: False, 2: False})
    assert x.equivalent(x).is_true
    assert x.if_then_else(y, ~y).evaluate({1: True, 2: True})
    with pytest.raises(TypeError):
        operator.truth(x)


def test_tseitin_cnf_tracks_and_eliminates_auxiliaries() -> None:
    manager = BddManager()
    root = (manager.variable(1) | manager.variable(2)) & manager.variable(3)
    encoding = root.to_cnf()

    assert len(encoding.formula) <= 4 * len(encoding.introduced_variables) + 1
    assert encoding.introduced_variables
    rebuilt = manager.from_cnf(encoding.formula)
    for variable in encoding.introduced_variables:
        rebuilt = rebuilt.exists(variable)
    assert rebuilt == root


def test_existing_cnf_imports_and_manager_mismatches_are_explicit() -> None:
    manager = BddManager()
    formula = Formula([Clause([1, -2]), Clause([2, 3])])
    root = manager.from_cnf(formula)
    assert root.evaluate({1: True, 2: False, 3: True})

    foreign = BddManager().variable(1)
    with pytest.raises(BddError):
        operator.and_(root, foreign)
