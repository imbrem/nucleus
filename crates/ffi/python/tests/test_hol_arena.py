"""The raw Ethane arena is wire data: it records rows and checks nothing.

Every constructor here appends a row and returns its one-based reference. The
only invariants an arena is allowed to have are representation invariants, so
these tests pin exactly two things: that the representation survives a CBOR
round trip byte for byte, and that no *logical* condition is imposed on the
way in. A raw arena that started rejecting ill-kinded rows would be a bug.
"""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Definition, Kernel, Link, Meta
from hol_invariants import import_depth, nested_import_arena, nested_import_cbor
from hol_support import arena_view, definition_view, meta_view

ONE_BASED = "one-based"


def populated() -> tuple[Arena, dict[str, int]]:
    """An arena holding one row of every tag, plus every side table."""
    arena = Arena()
    rows = {"kind.star": arena.kind_star()}
    star = rows["kind.star"]
    rows["kind.arr"] = arena.kind_arr(star, star)
    rows["ty.bool"] = arena.bool_ty()
    boolean = rows["ty.bool"]
    rows["ty.arr"] = arena.ty_arr(boolean, boolean)
    rows["ty.app"] = arena.ty_app(boolean, boolean)
    rows["ty.fv"] = arena.ty_fv(11, star)
    rows["ty.lam"] = arena.ty_lam(rows["ty.fv"], boolean)
    rows["tm.ty_exists"] = arena.ty_exists(12, boolean)
    rows["ty.model"] = arena.model(13, boolean)
    rows["tm.fv"] = arena.tm_fv(14, boolean)
    variable = rows["tm.fv"]
    rows["tm.app"] = arena.app(variable, variable)
    rows["tm.lam"] = arena.lam(variable, variable)
    rows["tm.bool"] = arena.bool(False)
    rows["tm.eq"] = arena.tm_eq(rows["tm.bool"], rows["tm.bool"])
    rows["tm.eps"] = arena.eps(boolean, variable)

    nested = Arena()
    nested.bool_ty()
    null = arena.add_null_import()
    literal = arena.add_literal_import(nested)
    link = arena.add_link_import(Link(O256.hash(b"import")))

    rows["tm.ref"] = arena.tm_ref(literal, rows["tm.bool"])
    rows["ty.ref"] = arena.ty_ref(link, boolean)
    rows["kind.ref"] = arena.kind_ref(null, star)

    arena.add_axiom("ax.zeta")
    arena.add_axiom("ax.alpha")
    arena.add_context(rows["tm.bool"])
    arena.add_context(rows["tm.eq"])
    arena.assume_valid(null)
    arena.assume_wf(literal, rows["tm.bool"], boolean)
    arena.assert_valid(link)
    arena.assert_wf(literal, boolean, star)
    return arena, rows


def test_every_constructor_appends_one_row_in_order() -> None:
    arena, rows = populated()

    assert list(rows.values()) == sorted(rows.values())
    assert len(arena) == len(rows)
    assert [row.reference for row in arena.definitions] == list(range(1, len(rows) + 1))
    assert {row.reference: row.tag for row in arena.definitions} == {
        reference: tag for tag, reference in rows.items()
    }


def test_rows_report_the_members_their_tag_carries() -> None:
    arena, rows = populated()
    by_tag = {row.tag: row for row in arena.definitions}

    assert by_tag["ty.fv"].name == 11
    assert by_tag["tm.ty_exists"].name == 12
    assert by_tag["ty.model"].name == 13
    assert by_tag["tm.fv"].name == 14
    assert by_tag["tm.bool"].value is False
    assert by_tag["tm.app"].children == [rows["tm.fv"], rows["tm.fv"]]
    assert by_tag["tm.eps"].children == [rows["ty.bool"], rows["tm.fv"]]
    # A proxy stores its import and foreign index instead of local children.
    assert (by_tag["tm.ref"].source, by_tag["tm.ref"].foreign) == (2, rows["tm.bool"])
    assert by_tag["tm.ref"].children == []
    # `eq` and `classifier` are the checked layer's members; raw rows omit them.
    assert {row.equal for row in arena.definitions} == {None}
    assert {row.classifier for row in arena.definitions} == {None}


def test_the_sort_of_a_tag_is_not_the_sort_of_its_constructor() -> None:
    """`model` builds a type and `ty_exists` builds a term, despite the names."""
    arena, rows = populated()

    assert arena.definition(rows["ty.model"]).tag == "ty.model"
    assert arena.definition(rows["tm.ty_exists"]).tag == "tm.ty_exists"


def test_lookup_is_one_based_and_bounded() -> None:
    arena, _ = populated()

    assert arena.definition(1).reference == 1
    assert arena.definition(len(arena)).reference == len(arena)
    assert arena.definition(len(arena) + 1) is None
    for outside_i32 in (2**31, 2**63, 2**64):
        with pytest.raises(OverflowError):
            arena.definition(outside_i32)
    with pytest.raises(ValueError, match=ONE_BASED):
        arena.definition(0)
    assert arena.definition(-1) is None


def test_definitions_agrees_with_pointwise_lookup() -> None:
    arena, _ = populated()

    assert [definition_view(row) for row in arena.definitions] == [
        definition_view(arena.definition(reference))
        for reference in range(1, len(arena) + 1)
    ]


def test_axioms_and_context_are_normalized_sets() -> None:
    arena = Arena()
    first = arena.bool(True)
    second = arena.bool(False)
    for _ in range(2):
        arena.add_axiom("ax.zeta")
        arena.add_axiom("ax.alpha")
        arena.add_context(second)
        arena.add_context(first)

    assert arena.axioms == ["ax.alpha", "ax.zeta"]
    assert arena.context == [first, second]


def test_the_raw_layer_accepts_axiom_names_the_kernel_refuses() -> None:
    """Nothing about an arena is a capability claim until something checks it."""
    arena = Arena()
    arena.add_axiom("ax.choice")
    arena.add_axiom("")

    assert arena.axioms == ["", "ax.choice"]


def test_metadata_keeps_insertion_order_and_duplicates() -> None:
    arena = Arena()
    source = arena.add_null_import()
    arena.assume_valid(source)
    arena.assume_valid(source)
    arena.assume_wf(source, 3, 4)
    arena.assert_wf(source, 4, 3)

    assert [meta_view(meta) for meta in arena.assumptions] == [
        ("meta.valid", source, None, None),
        ("meta.valid", source, None, None),
        ("meta.wf", source, 3, 4),
    ]
    assert [meta_view(meta) for meta in arena.assertions] == [("meta.wf", source, 4, 3)]


def test_nothing_logical_is_checked_on_the_way_in() -> None:
    """Dangling, cyclic, and ill-sorted rows are all representable."""
    arena = Arena()
    dangling = arena.kind_arr(900, 901)
    self_referential = arena.ty_arr(2, 2)
    ill_sorted = arena.app(dangling, self_referential)

    assert arena.definition(dangling).children == [900, 901]
    assert arena.definition(self_referential).children == [2, 2]
    assert arena.definition(ill_sorted).tag == "tm.app"
    assert arena.definition(900) is None
    assert Arena.from_cbor(arena.to_cbor()).addr() == arena.addr()


@pytest.mark.parametrize(
    "build",
    [
        lambda arena: arena.kind_arr(0, 1),
        lambda arena: arena.kind_arr(1, 0),
        lambda arena: arena.ty_arr(0, 1),
        lambda arena: arena.ty_app(0, 1),
        lambda arena: arena.ty_lam(0, 1),
        lambda arena: arena.ty_fv(0, 0),
        lambda arena: arena.ty_exists(0, 0),
        lambda arena: arena.model(0, 0),
        lambda arena: arena.tm_fv(0, 0),
        lambda arena: arena.app(0, 1),
        lambda arena: arena.lam(0, 1),
        lambda arena: arena.tm_eq(0, 1),
        lambda arena: arena.eps(0, 1),
        lambda arena: arena.add_context(0),
    ],
)
def test_zero_is_never_a_reference(build) -> None:
    with pytest.raises(ValueError, match=ONE_BASED):
        build(Arena())


@pytest.mark.parametrize(
    "build",
    [
        lambda arena: arena.tm_ref(0, 1),
        lambda arena: arena.ty_ref(0, 1),
        lambda arena: arena.kind_ref(0, 1),
        lambda arena: arena.assume_valid(0),
        lambda arena: arena.assert_valid(0),
        lambda arena: arena.assume_wf(0, 1, 1),
        lambda arena: arena.assert_wf(0, 1, 1),
    ],
)
def test_zero_is_never_an_import(build) -> None:
    with pytest.raises(ValueError, match="import IDs are one-based"):
        build(Arena())


@pytest.mark.parametrize("value", [1, 0, "true", None])
def test_boolean_literals_do_not_accept_other_types(value: object) -> None:
    """`bool` is the stored payload, not a truthiness test."""
    with pytest.raises(TypeError):
        Arena().bool(value)


@pytest.mark.parametrize("value", [True, False])
def test_boolean_literals_store_what_they_were_given(value: bool) -> None:
    arena = Arena()
    assert arena.definition(arena.bool(value)).value is value


def test_the_wire_form_round_trips_every_member() -> None:
    arena, _ = populated()
    decoded = Arena.from_cbor(arena.to_cbor())

    assert arena_view(decoded) == arena_view(arena)
    assert decoded.addr() == arena.addr()
    assert decoded.to_cbor() == arena.to_cbor()


def test_nested_literal_imports_round_trip_as_arenas() -> None:
    inner = Arena()
    inner.bool_ty()
    middle = Arena()
    middle.add_literal_import(inner)
    outer = Arena()
    outer.add_null_import()
    outer.add_literal_import(middle)
    outer.add_link_import(Link(O256.hash(b"leaf")))

    decoded = Arena.from_cbor(outer.to_cbor())
    null, literal, link = decoded.imports

    assert null is None
    assert isinstance(literal, Arena)
    assert isinstance(link, Link)
    assert arena_view(literal) == arena_view(middle)
    assert literal.imports[0].addr() == inner.addr()
    assert link.blake3 == O256.hash(b"leaf")
    assert link.format == "cbor"


def test_nested_literal_imports_round_trip_at_the_supported_limit() -> None:
    assert nested_import_cbor(0) == Arena().to_cbor()
    assert nested_import_cbor(3) == nested_import_arena(3).to_cbor()

    deep = Arena.from_cbor(nested_import_cbor(127))
    assert import_depth(deep) == 127
    assert deep.to_cbor() == nested_import_cbor(127)


def test_literal_import_construction_enforces_the_wire_depth_limit() -> None:
    deepest = nested_import_arena(127)

    with pytest.raises(ValueError, match="at most 127 levels"):
        Arena().add_literal_import(deepest)
    with pytest.raises(ValueError, match="at most 127 levels"):
        Kernel().import_literal(deepest)


def test_decoding_refuses_literal_imports_beyond_the_depth_limit() -> None:
    for depth in (128, 1_000, 20_000):
        with pytest.raises(ValueError, match="RecursionLimitExceeded"):
            Arena.from_cbor(nested_import_cbor(depth))


def test_the_import_getter_hands_back_copies() -> None:
    """Reaching into an import cannot edit the arena that holds it."""
    inner = Arena()
    inner.bool_ty()
    outer = Arena()
    outer.add_literal_import(inner)

    detached = outer.imports[0]
    detached.bool_ty()

    assert len(detached) == 2
    assert len(outer.imports[0]) == 1
    assert outer.imports[0] is not outer.imports[0]


def test_an_arena_cannot_import_itself() -> None:
    """PyO3's borrow check catches the aliasing rather than looping forever."""
    arena = Arena()
    with pytest.raises(RuntimeError, match="borrow"):
        arena.add_literal_import(arena)
    assert arena.imports == []


def test_addresses_track_content_and_nothing_else() -> None:
    left = Arena()
    right = Arena()
    assert left.addr() == right.addr()

    left.bool_ty()
    assert left.addr() != right.addr()
    right.bool_ty()
    assert left.addr() == right.addr()

    # Set members normalize, so insertion order cannot change the address.
    left.add_axiom("ax.a")
    left.add_axiom("ax.b")
    right.add_axiom("ax.b")
    right.add_axiom("ax.a")
    assert left.addr() == right.addr()

    # List members do not, so metadata order can.
    source = left.add_null_import()
    left.assume_valid(source)
    left.assume_wf(source, 1, 1)
    right.add_null_import()
    right.assume_wf(source, 1, 1)
    right.assume_valid(source)
    assert left.addr() != right.addr()


def test_addressing_is_pure() -> None:
    arena, _ = populated()
    assert arena.addr() == arena.addr()
    assert isinstance(arena.addr(), O256)


@pytest.mark.parametrize(
    "buffer", [b"", b"\x00\x01\x02", bytes([0xA1, 0x63, 0x74, 0x61, 0x67])]
)
def test_malformed_wire_input_is_a_value_error(buffer: bytes) -> None:
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(buffer)


def test_truncating_a_valid_encoding_is_rejected() -> None:
    arena, _ = populated()
    encoded = arena.to_cbor()

    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(encoded[: len(encoded) // 2])


@pytest.mark.parametrize("suffix", [b"\x00", b"junk", Arena().to_cbor()])
def test_decoding_rejects_trailing_bytes(suffix: bytes) -> None:
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(Arena().to_cbor() + suffix)


@pytest.mark.parametrize("wrap", [bytes, bytearray, memoryview])
def test_decoding_accepts_any_buffer(wrap) -> None:
    arena, _ = populated()
    encoded = arena.to_cbor()

    assert Arena.from_cbor(wrap(encoded)).addr() == arena.addr()


def test_decoding_rejects_text() -> None:
    with pytest.raises(TypeError):
        Arena.from_cbor("not bytes")


def test_snapshots_are_frozen_and_uninstantiable() -> None:
    arena, _ = populated()
    row = arena.definition(1)

    for opaque in (Definition, Meta):
        with pytest.raises(TypeError):
            opaque()
    with pytest.raises(AttributeError):
        row.tag = "kind.arr"
    with pytest.raises(AttributeError):
        row.reference = 2


def test_links_only_wrap_an_address() -> None:
    address = O256.hash(b"target")
    link = Link(address)

    assert link.format == "cbor"
    assert link.blake3 == address
    with pytest.raises(TypeError):
        Link(bytes(address))
    with pytest.raises(TypeError):
        Link()
