"""The Python LRAT API exposes only untrusted typed parsing."""

from covalence.logic.lrat import (
    RatGroup,
    Step,
    parse_binary,
    parse_text,
)
from covalence.logic.sat import Clause


def test_rat_groups_are_explicit_values() -> None:
    group = RatGroup(7, [1, 2])

    assert group.opposing_clause_id == 7
    assert group.resolvent_rup_hints == [1, 2]
    assert repr(group) == "RatGroup(7, [1, 2])"


def test_parsers_expose_typed_steps() -> None:
    text = parse_text("3 0 1 2 0\n4 d 1 2 0\n")
    binary = parse_binary(bytes([ord("a"), 6, 0, 2, 4, 0, ord("d"), 2, 4, 0]))

    assert isinstance(text[0], Step)
    assert text[0].clause == Clause([])
    assert text[0].ordered_hints == [1, 2]
    assert isinstance(text[1], Step)
    assert text[1].ids == [1, 2]
    assert len(binary) == 2
