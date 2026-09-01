#[path = "../compiler.rs"]
mod compiler;

use compiler::{Direction, Instruction};

#[test]
fn parses_the_bounded_language() {
    assert_eq!(
        compiler::parse("(rewrite-proposition forward)"),
        Ok(Instruction::RewriteProposition(Direction::Forward))
    );
    assert_eq!(
        compiler::parse("( rewrite-proposition\n backward )"),
        Ok(Instruction::RewriteProposition(Direction::Backward))
    );
}

#[test]
fn rejects_unknown_or_trailing_syntax() {
    for malformed in [
        "",
        "(rewrite forward)",
        "(rewrite-proposition sideways)",
        "(rewrite-proposition forward) extra",
        "rewrite-proposition forward",
        "(rewrite-proposition forward",
        "rewrite-proposition forward)",
        "((rewrite-proposition forward))",
    ] {
        assert!(
            compiler::parse(malformed).is_err(),
            "accepted {malformed:?}"
        );
    }
}

#[test]
fn lowering_selects_the_compiled_direction() {
    let generated = compiler::generate(Instruction::RewriteProposition(Direction::Backward));
    assert!(generated.contains("RewriteDirection::Backward"));
    assert!(!generated.contains("RewriteDirection::Forward"));
}
