use covalence_data_sexpr::{
    Atom, Document, Event, ExprKind, OneError, ParseError, Parser, SExprNode, StructureError,
    parse, parse_one,
};

#[test]
fn reads_every_atom_kind_and_preserves_spans() {
    let source = "(sym \"a\\nβ\" b\"\\0\\x01\\x02\\xff\" 123abc :key #define 'a)";
    let document = parse(source).unwrap();
    let ExprKind::List { items, .. } = document.expressions()[0].node() else {
        panic!("expected list");
    };
    assert!(matches!(items[0].node(), ExprKind::Atom { value: Atom::Symbol(v), .. } if v == "sym"));
    assert!(
        matches!(items[1].node(), ExprKind::Atom { value: Atom::String(v), .. } if v == "a\nβ")
    );
    assert!(
        matches!(items[2].node(), ExprKind::Atom { value: Atom::Bytes(v), .. } if v[..] == [0, 1, 2, 255])
    );
    assert!(
        matches!(items[3].node(), ExprKind::Atom { value: Atom::Number(v), .. } if v == "123abc")
    );
    assert!(
        matches!(items[4].node(), ExprKind::Atom { value: Atom::Keyword(v), .. } if v == "key")
    );
    assert!(
        matches!(items[5].node(), ExprKind::Atom { value: Atom::Directive(v), .. } if v == "define")
    );
    assert!(matches!(items[6].node(), ExprKind::Atom { value: Atom::Symbol(v), .. } if v == "'a"));
    assert_eq!(
        document.events().collect::<Vec<_>>(),
        Parser::new(source).collect::<Result<Vec<_>, _>>().unwrap()
    );
}

#[test]
fn comments_and_multiple_roots_are_documents() {
    let document = parse("; first\nalpha () ; last\n :answer").unwrap();
    assert_eq!(document.expressions().len(), 3);
    assert!(
        matches!(document.expressions()[0].node(), ExprKind::Atom { value: Atom::Symbol(v), .. } if v == "alpha")
    );
    assert!(
        matches!(document.expressions()[1].node(), ExprKind::List { items, .. } if items.is_empty())
    );
    assert!(
        matches!(document.expressions()[2].node(), ExprKind::Atom { value: Atom::Keyword(v), .. } if v == "answer")
    );
}

#[test]
fn byte_literals_cover_all_bytes_and_reject_malformed_source() {
    assert_eq!(
        Atom::encode_bytes(&[0, 1, 2, 255]),
        "b\"\\0\\x01\\x02\\xff\""
    );
    for invalid in [
        "b\"\\x0\"",
        "b\"\\xgg\"",
        "b\"\\q\"",
        "b\"β\"",
        "b\"line\nfeed\"",
    ] {
        assert!(matches!(
            parse_one(invalid),
            Err(OneError::Parse {
                source: ParseError::InvalidBytes { .. }
            })
        ));
    }
    assert!(
        matches!(parse_one("b\"\""), Ok(expression) if matches!(expression.node(), ExprKind::Atom { value: Atom::Bytes(value), .. } if value.is_empty()))
    );
    let all = (0..=u8::MAX).collect::<Vec<_>>();
    let expression = parse_one(&Atom::encode_bytes(&all)).unwrap();
    assert!(
        matches!(expression.node(), ExprKind::Atom { value: Atom::Bytes(value), .. } if value[..] == all)
    );
}

#[test]
fn malformed_text_has_typed_precise_errors() {
    assert_eq!(
        Parser::new(")").next(),
        Some(Err(ParseError::UnexpectedClose { span: 0..1 }))
    );
    assert!(matches!(parse("("), Err(ParseError::UnterminatedList { span }) if span == (1..1)));
    assert!(
        matches!(parse("\"abc"), Err(ParseError::UnterminatedString { span }) if span == (0..4))
    );
    assert!(matches!(parse("\"\\q\""), Err(ParseError::InvalidEscape { span }) if span == (1..3)));
    assert!(matches!(parse(":"), Err(ParseError::EmptyKeyword { .. })));
    assert!(matches!(parse("#"), Err(ParseError::EmptyDirective { .. })));
    assert!(matches!(parse_one(""), Err(OneError::Count { actual: 0 })));
    assert!(matches!(
        parse_one("a b"),
        Err(OneError::Count { actual: 2 })
    ));
}

#[test]
fn external_event_streams_are_checked() {
    assert_eq!(
        Document::from_events([Event::Close { span: 4..5 }]),
        Err(StructureError::UnexpectedCloseEvent { span: 4..5 })
    );
    assert_eq!(
        Document::from_events([Event::Open { span: 2..3 }]),
        Err(StructureError::UnterminatedListEvents { open: 2..3 })
    );
}

#[test]
fn spans_erase_into_the_spanless_template() {
    let document = parse("(alpha (beta))").unwrap();
    let erased = document.erase();
    let SExprNode::List { items, metadata } = erased.expressions()[0].node() else {
        panic!("expected erased list");
    };
    assert_eq!(*metadata, ());
    assert!(matches!(
        items[0].node(),
        SExprNode::Atom {
            value: Atom::Symbol(value),
            metadata: ()
        } if value == "alpha"
    ));
    assert_eq!(document.expressions()[0].erase(), erased.expressions()[0]);
}

#[test]
fn deeply_nested_reader_fold_and_traversal_are_iterative() {
    const DEPTH: usize = 20_000;
    let source = format!("{}x{}", "(".repeat(DEPTH), ")".repeat(DEPTH));
    let events = Parser::new(&source).collect::<Result<Vec<_>, _>>().unwrap();
    assert_eq!(events.len(), DEPTH * 2 + 1);
    let document = Document::from_events(events.clone()).unwrap();
    assert_eq!(document.events().collect::<Vec<_>>(), events);

    // Avoid recursively dropping a deliberately adversarial recursive value.
    std::mem::forget(document);
}
