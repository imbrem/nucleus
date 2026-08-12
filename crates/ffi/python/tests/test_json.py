"""`covalence.data.json`: strict construction, dict-like access, sharing."""

import math

import pytest
from covalence.data.json import InvalidJsonError, Json, dumps, loads

DOC = '{"alpha": {"nested": true}, "count": 3, "items": [1, "two", null]}'


# Construction and strictness


def test_loads_dumps_round_trips_canonically() -> None:
    doc = loads('{ "zeta" : 1,\n "alpha": [true, null] }')
    assert doc.dumps() == '{"alpha":[true,null],"zeta":1}'
    assert loads(doc.dumps()) == doc
    assert str(doc) == doc.dumps()


def test_pretty_output_is_indented() -> None:
    assert Json({"a": 1}).dumps(pretty=True) == '{\n  "a": 1\n}'


def test_duplicate_keys_are_an_error_not_a_last_wins() -> None:
    with pytest.raises(InvalidJsonError, match="duplicate object key"):
        loads('{"k": 1, "k": 2}')


def test_malformed_and_trailing_input_raise() -> None:
    for text in ["{", "nan", "'single'", "1 2", '{"a": 1,}']:
        with pytest.raises(InvalidJsonError):
            loads(text)


def test_construction_validates_rather_than_coerces() -> None:
    with pytest.raises(ValueError, match="non-finite"):
        Json(math.nan)
    with pytest.raises(ValueError, match="64 bits"):
        Json(2**64)
    with pytest.raises(TypeError, match="keys must be str"):
        Json({1: "x"})
    with pytest.raises(TypeError, match="cannot represent"):
        Json({"a": object()})
    assert Json(2**63).unwrap() == 2**63  # fits u64, stays exact


def test_stdlib_json_accepts_what_this_module_refuses() -> None:
    """The reason the class exists: `json` coerces, `Json` errors."""
    import json

    assert json.dumps(math.nan) == "NaN"  # not JSON at all
    assert json.loads('{"k": 1, "k": 2}') == {"k": 2}  # silent last-wins
    with pytest.raises(ValueError):
        Json(math.nan)


# Dict- and list-like access


def test_leaves_unwrap_and_containers_stay_wrapped() -> None:
    doc = loads(DOC)
    assert doc["count"] + 1 == 4
    assert isinstance(doc["alpha"], Json)
    assert doc["alpha"]["nested"] is True
    assert doc["items"][-1] is None


def test_subscript_errors_match_python_containers() -> None:
    doc = loads(DOC)
    with pytest.raises(KeyError):
        doc["missing"]
    with pytest.raises(IndexError):
        doc["items"][3]
    with pytest.raises(TypeError):
        doc[0]
    with pytest.raises(TypeError):
        doc["count"]["anything"]


def test_iteration_len_and_contains() -> None:
    doc = loads(DOC)
    assert len(doc) == 3
    assert list(doc) == ["alpha", "count", "items"]
    assert "count" in doc
    assert 1 not in doc  # non-str key is absent, not an error, as in a dict
    assert "two" in doc["items"]
    assert doc.get("count") == 3
    assert doc.get("missing", "fallback") == "fallback"
    assert doc.keys() == ["alpha", "count", "items"]
    assert doc.items()[1] == ("count", 3)
    assert doc.values()[1] == 3


def test_equality_converts_the_other_side() -> None:
    doc = loads(DOC)
    assert doc == {
        "alpha": {"nested": True},
        "count": 3,
        "items": [1, "two", None],
    }
    assert doc["items"] == [1, "two", None]
    assert doc != {"alpha": {}}
    assert doc != "unrelated"
    assert Json([1, 2]) != (1, 2)  # tuples hash unlike arrays, so never equal


def test_hash_agrees_with_equality() -> None:
    assert hash(Json(5)) == hash(5)
    assert hash(Json("text")) == hash("text")
    assert {Json(5): "found"}[5] == "found"
    a, b = loads('{"x": [1, {"y": 2}]}'), loads('{ "x" : [1, {"y": 2}] }')
    assert a == b and hash(a) == hash(b)


def test_truthiness_follows_python() -> None:
    assert not Json(None) and not Json(0) and not Json("") and not Json({})
    assert Json(0.5) and Json("x") and Json([0]) and Json({"a": None})


# Sharing and immutability


def test_subtrees_share_rather_than_copy() -> None:
    doc = loads(DOC)
    subtree = doc["alpha"]
    del doc
    assert subtree == {"nested": True}
    spliced = Json({"reused": subtree})  # splices the Arc, not a copy
    assert spliced["reused"]["nested"] is True


def test_json_is_immutable() -> None:
    doc = loads(DOC)
    with pytest.raises(TypeError):
        doc["count"] = 4
    with pytest.raises(AttributeError):
        doc.attribute = "anything"


def test_unwrap_produces_plain_python() -> None:
    doc = loads(DOC)
    plain = doc.unwrap()
    assert type(plain) is dict
    assert plain == {"alpha": {"nested": True}, "count": 3, "items": [1, "two", None]}
    assert Json(plain) == doc


# Odds and ends


def test_kind_names_the_variant() -> None:
    doc = loads(DOC)
    assert doc.kind == "object"
    assert doc["items"].kind == "array"
    assert Json(None).kind == "null"


def test_repr_round_trips_through_loads() -> None:
    doc = loads(DOC)
    assert repr(doc) == f"Json.loads('{doc.dumps()}')"
    assert eval(repr(doc), {"Json": Json}) == doc  # noqa: S307


def test_module_level_helpers_mirror_the_stdlib() -> None:
    assert dumps({"b": 1, "a": [True]}) == '{"a":[true],"b":1}'
    assert dumps({"a": 1}, pretty=True) == '{\n  "a": 1\n}'
    assert loads("[]") == []


def test_public_names_report_their_module() -> None:
    assert Json.__module__ == "covalence.data.json"
    assert InvalidJsonError.__module__ == "covalence.data.json"


def test_get_off_an_object_is_a_type_error() -> None:
    doc = loads(DOC)
    with pytest.raises(TypeError, match="has no get"):
        doc["items"].get("anything")


def test_number_equality_is_json_strict_not_python_lax() -> None:
    assert Json(1) == 1 and Json(1.0) == 1.0
    assert Json(1) != 1.0  # distinct JSON numbers, as they are distinct texts
    assert Json(1.0) != 1
    assert Json(1).unwrap() == 1.0  # unwrapped values follow Python again


def test_deep_nesting_is_refused_rather_than_overflowing() -> None:
    value: object = None
    for _ in range(1000):
        value = [value]
    with pytest.raises(ValueError, match="128 levels"):
        Json(value)
    # A deep Json spliced into a shallow shell costs no depth: it already fit.
    hundred = Json(loads("[" * 100 + "]" * 100))
    assert Json({"wrapped": hundred})["wrapped"] == hundred
