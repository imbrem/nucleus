"""Immutable userspace expressions remain outside the checked boundary."""

import operator

import pytest
from covalence.logic.expr import Context, DefaultConstructionHandler, Expr, Tm, Variable
from covalence.logic.hol import Kernel


def context() -> Context:
    return Context(Kernel())


def test_hierarchy_and_variable_metadata_are_immutable() -> None:
    construction = context()
    variable = construction.variable(7, construction.bool_type)

    assert isinstance(variable, Variable)
    assert isinstance(variable, Tm)
    assert isinstance(variable, Expr)
    assert variable.name == 7
    assert variable.type_reference == construction.bool_type
    assert construction.kernel.category(variable.reference) == "tm"
    with pytest.raises(AttributeError):
        variable.name = 8


def test_operators_construct_checked_conjunction_and_equality() -> None:
    construction = context()
    truth = construction.convert(True)
    conjunction = truth & False
    equality = operator.eq(truth, True)

    arena = construction.kernel.arena
    assert arena.definition(conjunction.reference).tag == "tm.op2.v1"
    assert arena.definition(equality.reference).tag == "tm.eq"
    assert (
        construction.kernel.classifier(conjunction.reference) == construction.bool_type
    )
    assert construction.kernel.classifier(equality.reference) == construction.bool_type
    assert truth.same_reference(truth)
    assert not truth.same_reference(construction.convert(True))


def test_reverse_and_converts_python_booleans() -> None:
    construction = context()
    term = True & construction.convert(False)
    assert construction.kernel.arena.definition(term.reference).tag == "tm.op2.v1"


def test_terms_cannot_cross_contexts_or_be_truth_tested() -> None:
    left = context().convert(True)
    right = context().convert(False)

    with pytest.raises(ValueError, match="different construction contexts"):
        left & right
    with pytest.raises(ValueError, match="different construction contexts"):
        operator.eq(left, right)
    with pytest.raises(TypeError, match="truth value"):
        bool(left)


def test_default_conversion_declines_other_python_domains() -> None:
    construction = context()
    for value in (1, 1.0, [True]):
        with pytest.raises(TypeError, match="cannot convert"):
            construction.convert(value)


def test_conversion_handler_is_extensible_without_kernel_authority() -> None:
    class ZeroOneHandler(DefaultConstructionHandler):
        def convert(self, construction, value, /):
            if type(value) is int and value in (0, 1):
                return super().convert(construction, bool(value))
            return super().convert(construction, value)

    construction = Context(Kernel(), ZeroOneHandler())
    equality = construction.convert(1) == 0

    assert construction.kernel.arena.definition(equality.reference).tag == "tm.eq"
    with pytest.raises(TypeError, match="cannot convert"):
        construction.convert(2)


def test_handler_cannot_smuggle_an_unchecked_object_into_a_term() -> None:
    class BrokenHandler(DefaultConstructionHandler):
        def convert(self, construction, value, /):
            return object()

    with pytest.raises(TypeError, match="must return Tm"):
        Context(Kernel(), BrokenHandler()).convert(True)


def test_operator_results_are_checked_after_custom_handler_dispatch() -> None:
    foreign = context().convert(True)

    class BrokenResultHandler(DefaultConstructionHandler):
        def conjunction(self, construction, left, right, /):
            return foreign

        def equality(self, construction, left, right, /):
            return object()

    construction = Context(Kernel(), BrokenResultHandler())
    truth = construction.convert(True)
    with pytest.raises(ValueError, match="different construction contexts"):
        truth & True
    with pytest.raises(TypeError, match="construct a Tm"):
        operator.eq(truth, True)
