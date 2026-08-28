use covalence_data_sexpr::{
    Atom, Document, ErasedRepr, Event, Expr, ExprKind, OneError, ParseError, Parser, Repr, SExpr,
    SExprNode, SharedRepr, SpannedRepr, StructureError, parse, parse_one,
};

fn atom(expression: &Expr) -> &Atom {
    let ExprKind::Atom(node) = expression.node() else {
        panic!("expected atom");
    };
    SpannedRepr::atom(node)
}

#[test]
fn reads_every_atom_kind_and_preserves_spans() {
    let source = "(sym \"a\\nβ\" b\"\\0\\x01\\x02\\xff\" 123abc :key #define 'a)";
    let document = parse(source).unwrap();
    let ExprKind::List(node) = document.expressions()[0].node() else {
        panic!("expected list");
    };
    let items = SpannedRepr::list_items(node);
    assert!(matches!(atom(&items[0]), Atom::Symbol(v) if v == "sym"));
    assert!(matches!(atom(&items[1]), Atom::String(v) if v == "a\nβ"));
    assert!(matches!(atom(&items[2]), Atom::Bytes(v) if v[..] == [0, 1, 2, 255]));
    assert!(matches!(atom(&items[3]), Atom::Number(v) if v == "123abc"));
    assert!(matches!(atom(&items[4]), Atom::Keyword(v) if v == "key"));
    assert!(matches!(atom(&items[5]), Atom::Directive(v) if v == "define"));
    assert!(matches!(atom(&items[6]), Atom::Symbol(v) if v == "'a"));
    assert_eq!(
        document.events().collect::<Vec<_>>(),
        Parser::new(source).collect::<Result<Vec<_>, _>>().unwrap()
    );
}

#[test]
fn comments_and_multiple_roots_are_documents() {
    let document = parse("; first\nalpha () ; last\n :answer").unwrap();
    assert_eq!(document.expressions().len(), 3);
    assert!(matches!(atom(&document.expressions()[0]), Atom::Symbol(v) if v == "alpha"));
    assert!(
        matches!(document.expressions()[1].node(), ExprKind::List(node) if SpannedRepr::list_items(node).is_empty())
    );
    assert!(matches!(atom(&document.expressions()[2]), Atom::Keyword(v) if v == "answer"));
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
        matches!(parse_one("b\"\""), Ok(expression) if matches!(atom(&expression), Atom::Bytes(value) if value.is_empty()))
    );
    let all = (0..=u8::MAX).collect::<Vec<_>>();
    let expression = parse_one(&Atom::encode_bytes(&all)).unwrap();
    assert!(matches!(atom(&expression), Atom::Bytes(value) if value[..] == all));
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
    let SExprNode::List(node) = erased.expressions()[0].node() else {
        panic!("expected erased list");
    };
    assert_eq!(*ErasedRepr::list_meta(node), ());
    let SExprNode::Atom(atom_node) = ErasedRepr::list_items(node)[0].node() else {
        panic!("expected erased atom");
    };
    assert_eq!(*ErasedRepr::atom_meta(atom_node), ());
    assert!(matches!(ErasedRepr::atom(atom_node), Atom::Symbol(value) if value == "alpha"));
    assert_eq!(document.expressions()[0].erase(), erased.expressions()[0]);
}

#[test]
fn shared_representation_configures_atom_type_and_node_metadata() {
    type Strings = SharedRepr<String, u8, &'static str>;

    let atom = SExpr::<Strings>::from_atom("custom".to_owned(), 7);
    let list = SExpr::<Strings>::from_list("list metadata", [atom]);
    let SExprNode::List(node) = list.node() else {
        panic!("expected list");
    };
    assert_eq!(Strings::list_meta(node), &"list metadata");
    let SExprNode::Atom(node) = Strings::list_items(node)[0].node() else {
        panic!("expected atom");
    };
    assert_eq!(Strings::atom(node), "custom");
    assert_eq!(Strings::atom_meta(node), &7);
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
