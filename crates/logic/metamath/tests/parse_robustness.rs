//! Conformance and hostile-input tests for the `.mm` reader.
//!
//! A Metamath database is third-party input by construction, so these cover the
//! cases where a reader that trusts its source misbehaves: unbounded `${`
//! nesting, tokens outside the spec's character classes, degenerate `$d`, `$c`
//! outside the outermost scope, and `$[ ... $]` in a position the spec does not
//! allow. Everything here goes through the public API only, so it stays valid
//! however the reader is implemented underneath.

use std::collections::HashMap;

use covalence_logic_metamath::{
    Database, MemoryResolver, MmError, Statement, parse, parse_into, parse_into_with_resolver,
    parse_with_resolver,
};

/// The `parse error: ...` text of an error the test expects to be one.
fn parse_error(result: Result<Database, MmError>) -> String {
    match result {
        Ok(_) => panic!("expected a parse error, got a database"),
        Err(e) => e.to_string(),
    }
}

fn resolver(files: &[(&str, &str)]) -> MemoryResolver {
    let map: HashMap<String, String> = files
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
        .collect();
    MemoryResolver::new(map)
}

// ---------------------------------------------------------------------------
// Unbounded `${ ... $}` nesting
// ---------------------------------------------------------------------------

/// The depth at which one stack frame per open block used to abort the process.
const DEEP: usize = 100_000;

#[test]
fn deeply_nested_scopes_do_not_overflow_the_stack() {
    let src = format!("$c a $.\n{}{}", "${ ".repeat(DEEP), "$} ".repeat(DEEP));
    let db = parse(&src).expect("balanced nesting is legal at any depth");
    assert!(db.is_symbol("a"));
}

#[test]
fn deeply_nested_unclosed_scopes_are_an_error_not_a_crash() {
    let src = format!("$c a $.\n{}", "${ ".repeat(DEEP));
    assert!(parse_error(parse(&src)).contains("unclosed `${`"));
}

#[test]
fn deeply_unmatched_scope_close_is_an_error_not_a_crash() {
    let src = format!("$c a $.\n{}", "$} ".repeat(DEEP));
    assert!(parse_error(parse(&src)).contains("unmatched `$}`"));
}

#[test]
fn scope_close_below_the_outermost_scope_is_rejected() {
    assert!(parse_error(parse("$c a $. ${ $} $}")).contains("unmatched `$}`"));
}

#[test]
fn unclosed_scope_is_rejected() {
    assert!(parse_error(parse("$c a $. ${ ${ $}")).contains("unclosed `${`"));
}

#[test]
fn balanced_nesting_still_scopes_hypotheses() {
    // The iterative block loop must still open and close sink scopes in step:
    // the scoped `$e` may not leak into the assertion that follows the block.
    let src = "$c wff |- $. $v ph $. wph $f wff ph $.\n\
               ${ h $e |- ph $. m $a |- ph $. $}\n\
               free $a |- ph $.\n";
    let db = parse(src).unwrap();
    let Some(Statement::Assert(free)) = db.statement_by_label("free") else {
        panic!("expected an assertion");
    };
    assert!(free.frame.essentials.is_empty());
}

// ---------------------------------------------------------------------------
// Label character class
// ---------------------------------------------------------------------------

#[test]
fn label_with_illegal_character_is_rejected() {
    let err = parse_error(parse("$c term 0 $. tz(e $a term 0 $."));
    assert!(err.contains("invalid label `tz(e`"), "{err}");
}

#[test]
fn label_may_use_every_character_the_spec_allows() {
    let db = parse("$c term 0 $. Ab9.x-y_Z $a term 0 $.").unwrap();
    assert!(db.statement_by_label("Ab9.x-y_Z").is_some());
}

#[test]
fn proof_step_with_illegal_character_is_rejected() {
    let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= tze* $.";
    let err = parse_error(parse(src));
    assert!(err.contains("invalid proof step label `tze*`"), "{err}");
}

#[test]
fn compressed_proof_label_with_illegal_character_is_rejected() {
    let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= ( tz|e ) AB $.";
    let err = parse_error(parse(src));
    assert!(
        err.contains("invalid compressed-proof label `tz|e`"),
        "{err}"
    );
}

#[test]
fn unterminated_compressed_label_block_stops_at_the_first_keyword() {
    // Without a label check the missing `)` swallowed the rest of the database
    // as proof text; now it is caught where it happens.
    let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= ( tze AB $. $c x $.";
    let err = parse_error(parse(src));
    assert!(err.contains("invalid compressed-proof label `$.`"), "{err}");
}

#[test]
fn compressed_proof_letter_block_is_left_to_the_verifier() {
    // The letter block is not a label list: its `A`-`Z`/`?` alphabet is the
    // decoder's business, so the reader must not reject letters here.
    let src = "$c term 0 $. tze $a term 0 $. th $p term 0 $= ( tze ) AB $.";
    assert!(parse(src).is_ok());
}

// ---------------------------------------------------------------------------
// Math symbol character class
// ---------------------------------------------------------------------------

#[test]
fn math_symbol_containing_a_dollar_is_rejected() {
    let err = parse_error(parse("$c a$b $."));
    assert!(err.contains("invalid math symbol `a$b`"), "{err}");
}

#[test]
fn non_ascii_math_symbol_is_rejected() {
    let err = parse_error(parse("$c \u{2192} $."));
    assert!(err.contains("invalid math symbol"), "{err}");
}

#[test]
fn control_character_in_a_math_symbol_is_rejected() {
    let err = parse_error(parse("$c a\u{7f}b $."));
    assert!(err.contains("invalid math symbol"), "{err}");
}

#[test]
fn math_symbols_may_use_punctuation_the_corpus_relies_on() {
    // `set.mm` symbols are far from alphanumeric; every printable ASCII
    // character other than `$` has to keep working.
    let src = "$c |- <-> [_ ]_ /\\ e. _V ( ) -> \"'\" ~P # $.";
    let db = parse(src).unwrap();
    assert!(db.is_symbol("<->"));
    assert!(db.is_symbol("/\\"));
    assert!(db.is_symbol("~P"));
}

#[test]
fn illegal_characters_are_rejected_in_every_symbol_position() {
    for src in [
        "$c a $. $v p$q $.",
        "$c wff $. $v ph $. wph $f wff p$h $.",
        "$c wff |- $. $v ph $. wph $f wff ph $. ${ h $e |- p$h $. $}",
        "$c wff |- $. $v ph $. wph $f wff ph $. ax $a |- p$h $.",
    ] {
        let err = parse_error(parse(src));
        assert!(err.contains("invalid math symbol"), "{src}: {err}");
    }
}

#[test]
fn comment_text_is_not_held_to_the_token_character_classes() {
    // A deliberate deviation from the spec's ASCII-only rule, documented in the
    // README: prose comments in real databases carry typographic characters.
    let db = parse("$( an em-dash \u{2014} and an accent \u{e9} $) $c a $.").unwrap();
    assert!(db.is_symbol("a"));
}

// ---------------------------------------------------------------------------
// `$d` arity
// ---------------------------------------------------------------------------

#[test]
fn disjoint_with_one_variable_is_rejected() {
    let src = "$c wff $. $v ph $. wph $f wff ph $. $d ph $.";
    let err = parse_error(parse(src));
    assert!(err.contains("`$d` needs two or more variables"), "{err}");
}

#[test]
fn empty_disjoint_is_rejected() {
    let err = parse_error(parse("$c wff $. $d $."));
    assert!(err.contains("`$d` needs two or more variables"), "{err}");
}

#[test]
fn disjoint_with_two_variables_is_accepted() {
    let src = "$c wff |- -> ( ) $. $v ph ps $.\n\
               wph $f wff ph $. wps $f wff ps $.\n\
               ${ $d ph ps $. ax $a |- ( ph -> ps ) $. $}\n";
    let db = parse(src).unwrap();
    let Some(Statement::Assert(ax)) = db.statement_by_label("ax") else {
        panic!("expected an assertion");
    };
    assert_eq!(ax.frame.disjoints.len(), 1);
}

// ---------------------------------------------------------------------------
// `$c` is confined to the outermost scope
// ---------------------------------------------------------------------------

#[test]
fn constant_declaration_inside_a_scope_is_rejected() {
    let err = parse_error(parse("$c wff $. ${ $c |- $. $}"));
    assert!(
        err.contains("`$c` is only allowed in the outermost scope"),
        "{err}"
    );
}

#[test]
fn constant_declaration_deep_inside_nested_scopes_is_rejected() {
    let err = parse_error(parse("$c wff $. ${ ${ ${ $c |- $. $} $} $}"));
    assert!(
        err.contains("`$c` is only allowed in the outermost scope"),
        "{err}"
    );
}

#[test]
fn constant_declaration_after_a_closed_scope_is_accepted() {
    // The depth counter has to come back down: `$c` after a balanced block is
    // outermost again.
    let db = parse("$c wff $. ${ $v ph $. $} $c |- $.").unwrap();
    assert!(db.is_symbol("|-"));
}

#[test]
fn variable_declaration_inside_a_scope_is_still_accepted() {
    // Only `$c` is confined; `$v` is legitimately scoped.
    let db = parse("$c wff $. ${ $v ph $. $}").unwrap();
    assert!(db.is_variable("ph"));
}

// ---------------------------------------------------------------------------
// `$[ ... $]` placement
// ---------------------------------------------------------------------------

#[test]
fn include_between_statements_is_accepted() {
    let files = resolver(&[
        ("root.mm", "$c wff $.\n$[ defs.mm $]\nwph $f wff ph $."),
        ("defs.mm", "$v ph $."),
    ]);
    let db = parse_with_resolver("root.mm", &files).unwrap();
    assert!(db.statement_by_label("wph").is_some());
}

#[test]
fn include_in_the_middle_of_a_statement_is_rejected() {
    let files = resolver(&[("root.mm", "$c a $[ defs.mm $] b $."), ("defs.mm", "")]);
    let err = parse_with_resolver("root.mm", &files)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("`$[` is only allowed between statements at the outermost scope"),
        "{err}"
    );
}

#[test]
fn include_between_a_label_and_its_keyword_is_rejected() {
    let files = resolver(&[
        (
            "root.mm",
            "$c wff $. $v ph $. wph $[ defs.mm $] $f wff ph $.",
        ),
        ("defs.mm", ""),
    ]);
    let err = parse_with_resolver("root.mm", &files)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("`$[` is only allowed between statements at the outermost scope"),
        "{err}"
    );
}

#[test]
fn include_inside_a_scope_is_rejected() {
    let files = resolver(&[("root.mm", "$c a $. ${ $[ defs.mm $] $}"), ("defs.mm", "")]);
    let err = parse_with_resolver("root.mm", &files)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("`$[` is only allowed between statements at the outermost scope"),
        "{err}"
    );
}

#[test]
fn include_inside_a_scope_an_earlier_file_opened_is_rejected() {
    // Scope depth is a property of the database, not of one file: an included
    // file that leaves a `${` open must not let the next include through.
    let files = resolver(&[
        ("root.mm", "$[ a.mm $] $[ b.mm $]"),
        ("a.mm", "$c x $. ${"),
        ("b.mm", "$c y $."),
    ]);
    let err = parse_with_resolver("root.mm", &files)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("`$[` is only allowed between statements at the outermost scope"),
        "{err}"
    );
}

#[test]
fn include_inside_a_proof_is_rejected() {
    let files = resolver(&[
        (
            "root.mm",
            "$c term 0 $. tze $a term 0 $. th $p term 0 $= tze $[ defs.mm $] $.",
        ),
        ("defs.mm", ""),
    ]);
    let err = parse_with_resolver("root.mm", &files)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("`$[` is only allowed between statements at the outermost scope"),
        "{err}"
    );
}

// ---------------------------------------------------------------------------
// The sink-driving entry points accept the same sources
// ---------------------------------------------------------------------------

#[test]
fn sink_entry_points_apply_the_same_rules() {
    let mut db = Database::new();
    assert!(parse_into("$c a $. ${ $c b $. $}", &mut db).is_err());

    let files = resolver(&[("root.mm", "$c a $[ defs.mm $] $."), ("defs.mm", "")]);
    let mut db = Database::new();
    assert!(parse_into_with_resolver("root.mm", &files, &mut db).is_err());
}
