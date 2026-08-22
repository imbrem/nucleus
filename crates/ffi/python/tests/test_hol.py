"""The public Ethane path keeps raw syntax separate from checked handles."""

import pytest
from covalence.logic.hol import Arena, Kernel, Kind, Link, Session, Tm, Ty


def test_raw_arena_roundtrip_and_normalized_sets() -> None:
    arena = Arena()
    bool_ty = arena.bool_ty()
    true = arena.bool(True)
    arena.add_axiom("ax.inf")
    arena.add_axiom("ax.inf")
    arena.add_context(true)
    arena.add_context(true)

    decoded = Arena.from_cbor(arena.to_cbor())
    assert decoded.address() == arena.address()
    assert decoded.axioms == ["ax.inf"]
    assert decoded.context == [true]
    assert decoded.definition(bool_ty).tag == "ty.bool"
    assert [definition.reference for definition in decoded.definitions] == [1, 2]
    with pytest.raises(ValueError, match="one-based"):
        decoded.definition(0)


def test_checked_handles_build_identity_beta_without_forging() -> None:
    session = Session()
    raw = Arena()
    bool_ty_ref = raw.bool_ty()
    kernel = session.check(raw)
    assert isinstance(kernel, Kernel)

    bool_ty = kernel.ty(bool_ty_ref)
    variable = kernel.tm_fv(7, bool_ty)
    identity = kernel.lam(variable, variable)
    true = kernel.bool(True)
    redex = kernel.app(identity, true)
    equality = kernel.assert_eq(redex, true)

    assert (equality.left, equality.right) == (redex.reference, true.reference)
    assert kernel.arena.definition(redex.reference).equal == true.reference

    other = session.check(Arena())
    with pytest.raises(ValueError, match="different kernel"):
        other.lam(variable, variable)
    for opaque in (Kernel, Kind, Ty, Tm):
        with pytest.raises(TypeError):
            opaque()


def test_literal_link_and_retryable_missing_import_agree() -> None:
    source = Arena()
    bool_ty = source.bool_ty()

    session = Session()
    address = session.store(source)
    linked = Arena()
    source_id = linked.add_link_import(Link(address))
    proxy = linked.ty_ref(source_id, bool_ty)
    assert session.resolve_sort(linked, proxy) == "ty"
    assert session.check(linked).ty(proxy).reference == proxy

    retry = Session()
    unresolved = Arena()
    source_id = unresolved.add_link_import(Link(address))
    proxy = unresolved.ty_ref(source_id, bool_ty)
    with pytest.raises(ValueError, match="Unavailable"):
        retry.resolve_sort(unresolved, proxy)
    assert retry.insert(source.to_cbor()) == address
    assert retry.resolve_sort(unresolved, proxy) == "ty"

    null = Arena()
    source_id = null.add_null_import()
    proxy = null.ty_ref(source_id, bool_ty)
    with pytest.raises(ValueError, match="NullImport"):
        retry.resolve_sort(null, proxy)


def test_imported_validity_is_checked_not_promoted_from_a_premise() -> None:
    session = Session()
    arena = Arena()
    source = arena.add_literal_import(Arena())
    arena.assume_valid(source)
    arena.assert_valid(source)
    checked = session.check(arena)

    assert checked.arena.assumptions[0].tag == "meta.valid"
    assert checked.arena.assertions[0].tag == "meta.valid"

    bad = Arena()
    source = bad.add_null_import()
    bad.assume_valid(source)
    bad.assert_valid(source)
    with pytest.raises(ValueError, match="NullImport"):
        session.check(bad)
