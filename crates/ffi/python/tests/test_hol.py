"""Tests for the indexed HolE syntax arena API."""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Expr, ImportTable, LinkRef, Segment


def test_expression_shape_and_arena_cbor_round_trip() -> None:
    arena = Arena()
    star = arena.push(Expr("KIND_STAR"))
    boolean = arena.push(Expr("TY_BOOL"))
    arrow = arena.push(Expr("TY_ARR", [boolean, boolean]))

    assert (star, boolean, arrow) == (1, 2, 3)
    assert [expr.tag for expr in arena.defs] == ["KIND_STAR", "TY_BOOL", "TY_ARR"]
    assert arena.defs[-1].ix == [2, 2]

    decoded = Arena.from_cbor(arena.to_cbor())
    assert decoded.to_cbor() == arena.to_cbor()
    assert [expr.tag for expr in decoded.defs] == ["KIND_STAR", "TY_BOOL", "TY_ARR"]


def test_expression_constructor_rejects_non_children_and_bad_variables() -> None:
    with pytest.raises(ValueError):
        Expr("TY_ARR", [0, 1])
    with pytest.raises(ValueError):
        Expr("TY_BOOL", [], 3)
    with pytest.raises(ValueError):
        Expr("TY_BV", [1], 0)


def test_arenas_form_a_lazy_import_graph() -> None:
    root = Arena()
    root.push(Expr("KIND_STAR"))
    assert isinstance(root.address(), O256)

    arena_imports = ImportTable()
    assert arena_imports.push(root.address()) == 0
    assert arena_imports.push(root.address()) == 0
    assert len(arena_imports) == 1
    assert isinstance(arena_imports.address(), O256)
    dependent = Arena(arena_imports.address())
    dependent.add_segment(Segment(1, 2, LinkRef(0, "cbor_dense", "arena"), 1))

    assert isinstance(dependent.address(), O256)
    assert Arena.from_cbor(dependent.to_cbor()).to_cbor() == dependent.to_cbor()
