"""The immutable CBOR Python surface."""

import operator

import pytest
from covalence.data.cbor import Cbor


def test_every_integer_round_trips_without_narrowing() -> None:
    for value in (0, -1, 2**64 - 1, 2**256, -(2**256)):
        encoded = Cbor.integer(value)
        assert encoded.kind == "integer"
        assert encoded.value == value


def test_compound_values_return_immutable_views() -> None:
    key = Cbor.text("answer")
    value = Cbor.integer(42)
    mapping = Cbor.map([(key, value), (key, value)])
    array = Cbor.array([mapping, Cbor.tag(24, Cbor.bytes(b"payload"))])

    assert isinstance(array.value, tuple)
    assert array.value[0].value == ((key, value), (key, value))
    assert array.value[1].value[0] == 24
    assert array.value[1].value[1].value == b"payload"


def test_scalar_encodings_remain_explicit() -> None:
    assert Cbor.bool(False) == Cbor.simple(20)
    assert Cbor.bool(True) == Cbor.simple(21)
    assert Cbor.null() == Cbor.simple(22)
    assert Cbor.undefined() == Cbor.simple(23)
    assert Cbor.float16(0x7E00).value == 0x7E00
    assert Cbor.float32(0x7FC00000).value == 0x7FC00000
    assert Cbor.float64(0x7FF8000000000000).value == 0x7FF8000000000000


def test_scalars_compare_directly_with_python_values() -> None:
    for value in (0, -1, 2**64 - 1, 2**256, -(2**256)):
        assert Cbor.integer(value) == value
        assert value == Cbor.integer(value)
    assert Cbor.bool(False) == False  # noqa: E712
    assert Cbor.bool(True) == True  # noqa: E712
    assert Cbor.null() == None  # noqa: E711
    assert Cbor.bytes(b"payload") == b"payload"
    assert Cbor.text("hello") == "hello"
    assert False == Cbor.bool(False)  # noqa: E712
    assert True == Cbor.bool(True)  # noqa: E712
    assert None == Cbor.null()  # noqa: E711
    assert b"payload" == Cbor.bytes(b"payload")
    assert "hello" == Cbor.text("hello")
    assert Cbor.integer(1) != True  # noqa: E712
    assert Cbor.simple(23) != None  # noqa: E711


def test_containers_compare_recursively_in_order() -> None:
    value = Cbor.array(
        [
            Cbor.integer(2**256),
            Cbor.map(
                [
                    (Cbor.text("first"), Cbor.bool(True)),
                    (Cbor.text("second"), Cbor.null()),
                ]
            ),
        ]
    )
    assert value == [2**256, {"first": True, "second": None}]
    assert [2**256, {"first": True, "second": None}] == value
    assert value != [2**256, {"second": None, "first": True}]

    duplicate_keys = Cbor.map(
        [
            (Cbor.text("key"), Cbor.integer(1)),
            (Cbor.text("key"), Cbor.integer(2)),
        ]
    )
    assert duplicate_keys != {"key": 2}


def test_values_are_immutable_and_unhashable() -> None:
    value = Cbor.integer(1)
    with pytest.raises(AttributeError):
        value.value = 2
    with pytest.raises(TypeError):
        hash(value)
    with pytest.raises(TypeError):
        operator.lt(value, Cbor.integer(2))


def test_constructor_types_and_widths_are_checked() -> None:
    with pytest.raises(TypeError):
        Cbor.integer("1")
    with pytest.raises(OverflowError):
        Cbor.simple(256)
    with pytest.raises(OverflowError):
        Cbor.float16(2**16)
