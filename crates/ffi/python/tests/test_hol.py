"""Tests for indexed HolE arenas and sequents."""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Ctx, Expr, ImportTable, LinkRef, Segment, Seq


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


def test_term_payloads_are_typed_and_round_trip() -> None:
    bound = Expr("TM_BV", var=4)
    free = Expr("TM_FV", [1], var=5)
    truth = Expr("TM_BOOL", value=True)

    assert (bound.var, free.var, free.ix, truth.value) == (4, 5, [1], True)
    assert Expr("TM_EQ", [1, 2]).ix == [1, 2]
    with pytest.raises(ValueError):
        Expr("TM_EQ", [1, 2, 3])
    with pytest.raises(ValueError):
        Expr("TM_BOOL", var=1)
    with pytest.raises(ValueError):
        Expr("TM_BV", value=False)

    two_fifty_six = Expr("TM_NAT", data=b"\x01\x00")
    assert two_fifty_six.data == b"\x01\x00"
    with pytest.raises(ValueError):
        Expr("TM_NAT", data=b"\x00\x01")

    payload = Expr("TM_BYTES", data=b"\x00HolE\xff")
    assert payload.data == b"\x00HolE\xff"


def test_arenas_and_sequents_form_a_lazy_import_graph() -> None:
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

    first_imports = ImportTable()
    assert first_imports.push(dependent.address()) == 0
    first = Seq(LinkRef(0, "cbor_dense", "arena"), first_imports.address())

    second_imports = ImportTable()
    assert second_imports.push(dependent.address()) == 0
    assert second_imports.push(first.address()) == 1
    second = Seq(LinkRef(0, "cbor_dense", "arena"), second_imports.address())
    assert second.assume(LinkRef(1, "cbor_sparse", "sequent"))
    assert isinstance(second.address(), O256)

    assert Seq.from_cbor(second.to_cbor()).to_cbor() == second.to_cbor()


def test_contexts_materialize_and_repack_every_sequent_fact() -> None:
    arena = LinkRef(0, "cbor_dense", "arena")
    imported = LinkRef(1, "cbor_sparse", "sequent")
    premises = Ctx(arena)
    assert premises.insert_sequent(imported)
    assert premises.insert("has_ty", 1, 2)
    assert premises.insert_symmetric("ty_eq", 2, -3)
    assert premises.contains("ty_eq", -3, 2)
    assert premises.pairs("ty_eq") == [(-3, 2), (2, -3)]

    conclusions = Ctx(arena)
    assert conclusions.insert("imp", 0, 1)
    sequent = Seq.from_contexts(premises, conclusions)
    assert sequent.premises.to_cbor() == premises.to_cbor()
    assert sequent.conclusion.to_cbor() == conclusions.to_cbor()
    assert sequent.premise_pairs("has_ty") == [(1, 2)]
    assert sequent.conclusion_pairs("imp") == [(0, 1)]
    assert Seq.from_premises(premises).premises.to_cbor() == premises.to_cbor()
    assert (
        Seq.from_conclusion(conclusions).conclusion.to_cbor() == conclusions.to_cbor()
    )

    with pytest.raises(ValueError, match="different arenas"):
        Seq.from_contexts(premises, Ctx())
    with pytest.raises(ValueError, match="i32::MIN"):
        premises.insert("eq", -(2**31), 1)
    with pytest.raises(ValueError, match="directional"):
        premises.insert_symmetric("imp", 1, 2)


def test_static_init_arena_is_literal_free_and_hash_pinned() -> None:
    arena = Arena.init()
    assert len(arena) == 132
    assert all(expr.tag not in {"TM_NAT", "TM_BYTES"} for expr in arena.defs)
    assert Arena.from_cbor(arena.to_cbor()).to_cbor() == arena.to_cbor()
    assert str(arena.address()) == (
        "bd45466292e106cf30b9e596e4432058e18141460b9032d740c034ef614709ed"
    )
