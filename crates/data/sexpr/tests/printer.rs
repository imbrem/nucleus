use bytes::Bytes;
use covalence_data_sexpr::{Atom, Expr, ExprKind, Printer, Repr, SpannedRepr, parse, parse_one};

#[test]
fn flat_and_broken_layouts_are_width_sensitive_and_parse_back() {
    let expression = parse_one("(define option (lambda x (some x)))").unwrap();
    let flat = Printer {
        width: 80,
        indent: 2,
    }
    .expression(&expression)
    .unwrap();
    let broken = Printer {
        width: 18,
        indent: 2,
    }
    .expression(&expression)
    .unwrap();

    assert_eq!(flat, "(define option (lambda x (some x)))");
    assert_eq!(
        broken,
        "(define\n  option\n  (lambda\n    x\n    (some x)))"
    );
    assert_eq!(
        parse_one(&flat).unwrap().events().count(),
        expression.events().count()
    );
    assert_eq!(
        parse_one(&broken).unwrap().events().count(),
        expression.events().count()
    );
}

#[test]
fn every_atom_kind_has_a_canonical_round_trip_spelling() {
    let source = "symbol \"text\\nβ\" b\"A\\0\\xff\" 123x :key #define !(AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=)";
    let document = parse(source).unwrap();
    let printed = Printer::default().document(&document).unwrap();
    let reparsed = parse(&printed).unwrap();
    let values = |document: &covalence_data_sexpr::Document| {
        document
            .events()
            .filter_map(|event| match event {
                covalence_data_sexpr::Event::Atom { value, .. } => Some(value),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(values(&reparsed), values(&document));
}

#[test]
fn arbitrary_bytes_print_readably_and_round_trip() {
    let expression = Expr::atom(Atom::Bytes(Bytes::from_static(b"hello\0\xff")), 0..0);
    let printed = Printer::default().expression(&expression).unwrap();
    assert_eq!(printed, "b\"hello\\0\\xff\"");
    assert!(matches!(
        parse_one(&printed).unwrap().node(),
        ExprKind::Atom(node) if matches!(SpannedRepr::atom(node), Atom::Bytes(value) if value[..] == *b"hello\0\xff")
    ));
}

#[test]
fn invalid_constructed_atom_kinds_are_rejected() {
    let expression = Expr::atom(Atom::Symbol("123".into()), 0..0);
    assert!(Printer::default().expression(&expression).is_err());
}
