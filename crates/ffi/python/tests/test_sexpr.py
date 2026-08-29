"""The owned S-expression Python surface."""

import pytest
from covalence.data.sexpr import (
    Atom,
    Document,
    ErasedDocument,
    ErasedSExpr,
    Event,
    SExpr,
    parse,
    parse_events,
    parse_one,
)


def test_atoms_keep_fixed_kinds_and_python_values() -> None:
    expression = parse_one(
        '(name "text\\n" b"A\\x00\\xff" 123x :key #define '
        "!0000000000000000000000000000000000000000000000000000000000000000)"
    )
    values = expression.items
    assert [(value.atom_value.kind, value.atom_value.value) for value in values] == [
        ("symbol", "name"),
        ("string", "text\n"),
        ("bytes", b"A\x00\xff"),
        ("number", "123x"),
        ("keyword", "key"),
        ("directive", "define"),
        ("o256", bytes(32)),
    ]

    assert Atom.o256(bytes(32)).value == bytes(32)
    with pytest.raises(ValueError):
        Atom.o256(bytes(31))


def test_documents_and_events_round_trip() -> None:
    source = "; comment\n(a) :b"
    document = parse(source)
    events = parse_events(source)
    assert len(document) == 2
    assert [event.kind for event in events] == ["open", "atom", "close", "atom"]
    rebuilt = Document.from_events(events)
    assert [event.span for event in rebuilt.events()] == [
        event.span for event in events
    ]
    assert rebuilt.expressions[0].items[0].atom_value.value == "a"


def test_python_can_construct_ast_and_events() -> None:
    atom = Atom.symbol("x")
    expression = SExpr.list([SExpr.atom(atom)], open=(1, 2), close=(3, 4))
    assert [(event.kind, event.span) for event in expression.events()] == [
        ("open", (1, 2)),
        ("atom", (0, 0)),
        ("close", (3, 4)),
    ]
    assert (
        Document.from_events(expression.events())
        .expressions[0]
        .items[0]
        .atom_value.value
        == "x"
    )


def test_spans_erase_to_distinct_spanless_types() -> None:
    spanned = parse("(x)")
    erased = spanned.erase()
    assert isinstance(erased, ErasedDocument)
    assert isinstance(erased.expressions[0], ErasedSExpr)
    assert erased.expressions[0].items[0].atom_value.value == "x"
    assert not hasattr(erased.expressions[0], "span")
    assert spanned.expressions[0].erase().items[0].atom_value.value == "x"

    constructed = ErasedDocument(
        [ErasedSExpr.list([ErasedSExpr.atom(Atom.symbol("y"))])]
    )
    assert constructed.expressions[0].items[0].atom_value.value == "y"


def test_malformed_source_and_event_streams_raise_value_error() -> None:
    for source in (")", "(", '"bad', 'b"β"', 'b"\\x0"', ":", "#"):
        with pytest.raises(ValueError):
            parse(source)
    with pytest.raises(ValueError):
        Document.from_events([Event.close(0, 1)])


def test_event_reader_has_no_arbitrary_nesting_limit() -> None:
    depth = 20_000
    events = parse_events("(" * depth + "x" + ")" * depth)
    assert len(events) == depth * 2 + 1


def test_width_aware_formatting_round_trips() -> None:
    expression = parse_one("(define option (lambda x (some x)))")
    assert expression.format() == "(define option (lambda x (some x)))"
    broken = expression.format(width=18)
    assert broken == "(define\n  option\n  (lambda\n    x\n    (some x)))"
    assert [event.kind for event in parse_one(broken).events()] == [
        event.kind for event in expression.events()
    ]
