"""The raw Ethane arena is wire data, and only wire data.

`Arena` is the untrusted half of the two-layer API: it accepts whatever a
caller or a decoder hands it and promises nothing beyond the representation
invariants. These tests pin down both halves of that bargain — the structure
it does guarantee, and the nonsense it is required to tolerate.
"""

import pytest
from covalence.lib.hash import O256
from covalence.logic.hol import Arena, Definition, Kernel, Link, Meta
from hol_support import (
    EMPTY_ARENA_CBOR,
    RAW_REFERENCE_CALLS,
    assert_arena_invariants,
    call_names,
    definitions_by_reference,
    import_depth,
    nested_import_arena,
    nested_import_cbor,
    roundtrip,
)


def test_the_empty_arena_has_a_fixed_wire_form() -> None:
    """The encoding is the object's identity, so it is pinned literally."""
    arena = Arena()
    assert len(arena) == 0
    assert arena.to_cbor() == EMPTY_ARENA_CBOR
    assert arena.definitions == []
    assert arena.imports == []
    assert arena.axioms == []
    assert arena.context == []
    assert arena.assumptions == []
    assert arena.assertions == []
    assert Arena.from_cbor(EMPTY_ARENA_CBOR).addr() == arena.addr()


def test_every_raw_constructor_appends_a_dense_one_based_row() -> None:
    arena = Arena()
    star = arena.kind_star()
    kind_arr = arena.kind_arr(star, star)
    bool_ty = arena.bool_ty()
    ty_arr = arena.ty_arr(bool_ty, bool_ty)
    ty_fv = arena.ty_fv(11, star)
    ty_app = arena.ty_app(ty_fv, bool_ty)
    ty_lam = arena.ty_lam(ty_fv, bool_ty)
    truth = arena.bool(True)
    ty_exists = arena.ty_exists(12, truth)
    model = arena.model(13, truth)
    tm_fv = arena.tm_fv(14, bool_ty)
    app = arena.app(tm_fv, truth)
    lam = arena.lam(tm_fv, truth)
    tm_eq = arena.tm_eq(truth, truth)
    eps = arena.eps(bool_ty, tm_fv)
    source = arena.add_null_import()
    tm_ref = arena.tm_ref(source, bool_ty)
    ty_ref = arena.ty_ref(source, bool_ty)
    kind_ref = arena.kind_ref(source, bool_ty)

    order = [
        star,
        kind_arr,
        bool_ty,
        ty_arr,
        ty_fv,
        ty_app,
        ty_lam,
        truth,
        ty_exists,
        model,
        tm_fv,
        app,
        lam,
        tm_eq,
        eps,
        tm_ref,
        ty_ref,
        kind_ref,
    ]
    assert order == list(range(1, len(order) + 1))
    assert len(arena) == len(order)

    rows = definitions_by_reference(arena)
    assert [rows[reference].tag for reference in order] == [
        "kind.star",
        "kind.arr",
        "ty.bool",
        "ty.arr",
        "ty.fv",
        "ty.app",
        "ty.lam",
        "tm.bool",
        "tm.ty_exists",
        "ty.model",
        "tm.fv",
        "tm.app",
        "tm.lam",
        "tm.eq",
        "tm.eps",
        "tm.ref",
        "ty.ref",
        "kind.ref",
    ]
    assert rows[kind_arr].children == [star, star]
    assert rows[ty_fv].children == [star]
    assert rows[ty_fv].name == 11
    assert rows[truth].value is True
    assert rows[ty_exists].name == 12
    assert rows[model].name == 13
    assert rows[eps].children == [bool_ty, tm_fv]
    assert (rows[tm_ref].source, rows[tm_ref].foreign) == (source, bool_ty)
    assert rows[star].children == []
    assert_arena_invariants(arena)


def test_rows_carry_no_checked_members() -> None:
    """Raw rows have neither an equality parent nor a classifier."""
    arena = Arena()
    arena.kind_star()
    arena.bool_ty()
    for definition in arena.definitions:
        assert definition.equal is None
        assert definition.classifier is None


def test_row_snapshots_are_immutable_and_detached() -> None:
    arena = Arena()
    truth = arena.bool(True)
    snapshot = arena.definition(truth)
    assert isinstance(snapshot, Definition)
    with pytest.raises(AttributeError):
        snapshot.tag = "tm.bool"  # type: ignore[misc]
    with pytest.raises(AttributeError):
        snapshot.children = [1]  # type: ignore[misc]

    # A list getter hands out a fresh list; editing it cannot edit the row.
    children = snapshot.children
    children.append(99)
    assert snapshot.children == []

    arena.bool(False)
    assert snapshot.reference == truth
    assert snapshot.value is True


def test_axioms_and_context_are_normalized_sets() -> None:
    arena = Arena()
    first = arena.bool(True)
    second = arena.bool(False)
    for name in ("ax.z", "ax.a", "ax.z"):
        arena.add_axiom(name)
    for reference in (second, first, second):
        arena.add_context(reference)

    assert arena.axioms == ["ax.a", "ax.z"]
    assert arena.context == [first, second]
    assert roundtrip(arena).axioms == arena.axioms
    assert roundtrip(arena).context == arena.context


def test_metadata_is_an_ordered_log_and_keeps_its_shape() -> None:
    arena = Arena()
    arena.assume_valid(1)
    arena.assume_wf(2, 3, 4)
    arena.assert_wf(5, 6, 7)
    arena.assert_valid(8)

    assumptions = arena.assumptions
    assertions = arena.assertions
    assert all(isinstance(entry, Meta) for entry in assumptions + assertions)
    assert [entry.tag for entry in assumptions] == ["meta.valid", "meta.wf"]
    assert [entry.tag for entry in assertions] == ["meta.wf", "meta.valid"]
    assert (assumptions[0].source, assumptions[0].reference) == (1, None)
    assert assumptions[0].classifier is None
    assert (assumptions[1].source, assumptions[1].reference) == (2, 3)
    assert assumptions[1].classifier == 4
    assert (assertions[0].source, assertions[0].reference) == (5, 6)
    assert assertions[0].classifier == 7

    decoded = roundtrip(arena)
    assert [entry.tag for entry in decoded.assumptions] == ["meta.valid", "meta.wf"]
    assert decoded.assertions[0].classifier == 7


def test_duplicate_metadata_is_kept_because_it_is_a_log_not_a_set() -> None:
    arena = Arena()
    arena.assume_valid(1)
    arena.assume_valid(1)
    assert len(arena.assumptions) == 2
    assert len(roundtrip(arena).assumptions) == 2


def test_imports_keep_their_three_shapes() -> None:
    inner = Arena()
    inner.kind_star()
    address = inner.addr()

    arena = Arena()
    null = arena.add_null_import()
    literal = arena.add_literal_import(inner)
    link = arena.add_link_import(Link(address))
    assert (null, literal, link) == (1, 2, 3)

    entries = arena.imports
    assert entries[0] is None
    assert isinstance(entries[1], Arena)
    assert entries[1].addr() == address
    assert isinstance(entries[2], Link)
    assert entries[2].format == "cbor"
    assert entries[2].blake3 == address

    decoded = roundtrip(arena)
    assert decoded.imports[0] is None
    assert isinstance(decoded.imports[1], Arena)
    assert decoded.imports[1].addr() == address
    assert decoded.imports[2].blake3 == address


def test_a_literal_import_is_a_copy_not_an_alias() -> None:
    inner = Arena()
    arena = Arena()
    arena.add_literal_import(inner)
    before = arena.addr()

    inner.kind_star()
    assert arena.addr() == before
    assert len(arena.imports[0]) == 0

    # Reading an import back also copies, so edits to the copy stay local.
    copy = arena.imports[0]
    copy.kind_star()
    assert arena.addr() == before


def test_links_are_content_addresses_not_resolutions() -> None:
    address = O256.hash(b"not an arena")
    link = Link(address)
    assert link.blake3 == address
    assert link.format == "cbor"

    arena = Arena()
    arena.add_link_import(link)
    # Nothing resolves it, so an address naming no object is still wire data.
    assert roundtrip(arena).imports[0].blake3 == address


def test_the_address_tracks_the_current_contents() -> None:
    arena = Arena()
    empty = arena.addr()
    assert arena.addr() == empty

    arena.kind_star()
    with_row = arena.addr()
    assert with_row != empty

    arena.add_axiom("ax.inf")
    assert arena.addr() != with_row

    twin = Arena()
    twin.kind_star()
    twin.add_axiom("ax.inf")
    assert twin.addr() == arena.addr()
    assert twin.to_cbor() == arena.to_cbor()


def test_row_order_is_part_of_the_address() -> None:
    left = Arena()
    left.kind_star()
    left.bool_ty()

    right = Arena()
    right.bool_ty()
    right.kind_star()

    assert left.addr() != right.addr()


@pytest.mark.parametrize(
    ("name", "call"),
    RAW_REFERENCE_CALLS,
    ids=call_names(RAW_REFERENCE_CALLS),
)
def test_every_raw_index_rejects_zero(name: str, call) -> None:
    arena = Arena()
    arena.kind_star()
    with pytest.raises(ValueError, match="one-based"):
        call(arena)


def test_dangling_references_are_representable_by_design() -> None:
    """Decoding establishes no kinding, typing, or even row existence."""
    arena = Arena()
    dangling = arena.kind_arr(9, 9)
    arena.add_context(7)
    arena.assume_wf(4, 5, 6)
    arena.tm_ref(3, 2)

    assert arena.definition(dangling).children == [9, 9]
    assert arena.definition(9) is None
    assert arena.context == [7]

    decoded = roundtrip(arena)
    assert decoded.definition(dangling).children == [9, 9]
    assert decoded.context == [7]
    assert decoded.addr() == arena.addr()
    assert_arena_invariants(arena)


def test_raw_axiom_names_are_not_checked() -> None:
    """Only the kernel decides which capabilities exist."""
    arena = Arena()
    arena.add_axiom("ax.does.not.exist")
    arena.add_axiom("")
    assert arena.axioms == ["", "ax.does.not.exist"]
    assert roundtrip(arena).axioms == arena.axioms


@pytest.mark.parametrize(
    "payload",
    [
        pytest.param(b"", id="empty"),
        pytest.param(b"\xff\xff\xff", id="not-cbor"),
        pytest.param(b"\x80", id="array-not-map"),
        pytest.param(b"\xa0", id="empty-map"),
        pytest.param(EMPTY_ARENA_CBOR[:-1], id="truncated"),
    ],
)
def test_malformed_wire_data_raises_instead_of_crashing(payload: bytes) -> None:
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(payload)


@pytest.mark.parametrize(
    "suffix",
    [
        pytest.param(b"\x00", id="one-byte"),
        pytest.param(b"garbage" * 100, id="junk"),
        pytest.param(EMPTY_ARENA_CBOR, id="second-arena"),
    ],
)
@pytest.mark.xfail(
    reason="from_cbor decodes a prefix and ignores trailing bytes",
    strict=False,
)
def test_trailing_bytes_are_rejected(suffix: bytes) -> None:
    """Decoding a prefix makes the encoding non-injective, which is a defect.

    An arena's address is the hash of its encoding, so a decoder that ignores
    whatever follows a complete object admits unlimited distinct byte strings
    — with unlimited distinct addresses — that all decode to the same arena.
    Marked expected-failure rather than deleted: it should start passing once
    `from_cbor` requires the reader to be exhausted.
    """
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(EMPTY_ARENA_CBOR + suffix)


def test_a_decoded_prefix_still_re_encodes_to_the_prefix() -> None:
    """Today's behaviour, recorded so the defect above has a precise shape."""
    padded = EMPTY_ARENA_CBOR + b"\x00"
    decoded = Arena.from_cbor(padded)
    assert decoded.to_cbor() == EMPTY_ARENA_CBOR
    assert decoded.addr() == Arena().addr()
    assert decoded.to_cbor() != padded


def test_a_wrong_tag_is_rejected() -> None:
    payload = EMPTY_ARENA_CBOR.replace(b"\x65arena", b"\x65arenb")
    assert payload != EMPTY_ARENA_CBOR
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(payload)


def test_unknown_fields_are_rejected() -> None:
    """`deny_unknown_fields` is what keeps the encoding exact."""
    extended = b"\xa8" + EMPTY_ARENA_CBOR[1:] + b"\x63new\x80"
    with pytest.raises(ValueError, match="invalid Ethane arena"):
        Arena.from_cbor(extended)


def test_from_cbor_accepts_any_buffer() -> None:
    assert Arena.from_cbor(bytearray(EMPTY_ARENA_CBOR)).addr() == Arena().addr()
    assert Arena.from_cbor(memoryview(EMPTY_ARENA_CBOR)).addr() == Arena().addr()


def test_nested_imports_round_trip_up_to_the_decoder_limit() -> None:
    """The hand-built wire form matches what the API produces."""
    assert nested_import_cbor(0) == EMPTY_ARENA_CBOR
    assert nested_import_cbor(3) == nested_import_arena(3).to_cbor()

    deep = Arena.from_cbor(nested_import_cbor(127))
    assert import_depth(deep) == 127
    assert deep.to_cbor() == nested_import_cbor(127)


def test_encoding_can_outrun_decoding(request: pytest.FixtureRequest) -> None:
    """`to_cbor` produces bytes `from_cbor` refuses, which is a real defect.

    128 nested literal imports is the decoder's ciborium recursion limit. The
    encoder has no matching bound, so an arena one level past it — reachable
    with a single `add_literal_import`, and accepted by `Kernel.import_literal`
    — encodes to bytes nothing can read back. Marked expected-failure rather
    than deleted: it should start passing when the two limits are reconciled.
    """
    request.node.add_marker(
        pytest.mark.xfail(
            reason="the encoder has no depth bound matching the decoder's",
            strict=False,
        )
    )
    encoded = nested_import_arena(128).to_cbor()
    assert Arena.from_cbor(encoded).to_cbor() == encoded


def test_decoding_refuses_unbounded_nesting_instead_of_recursing() -> None:
    """The decoder is the side that faces untrusted bytes, and it is bounded."""
    for depth in (128, 1_000, 20_000):
        with pytest.raises(ValueError, match="RecursionLimitExceeded"):
            Arena.from_cbor(nested_import_cbor(depth))


def test_a_raw_arena_is_not_a_kernel() -> None:
    """Nothing on the raw layer can be mistaken for checked construction."""
    arena = Arena()
    assert not hasattr(arena, "star")
    assert not hasattr(arena, "union_syn_fact")
    assert not hasattr(arena, "syn_refl")
    assert not hasattr(arena, "category")
    assert not hasattr(Kernel(), "kind_star")
