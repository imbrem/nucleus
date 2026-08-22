//! The `hol-ax.mm` fixture: hol.mm's axioms with the development stripped off.
//!
//! Two things are being checked, and they are not the same thing.
//!
//! [`fixture_is_an_axiom_only_database`] and its neighbours run everywhere.
//! They pin what the fixture *is* — 71 unproved assertions, named, with the
//! declarations and hypotheses that make them well-formed — so that an edit to
//! the file has to be a deliberate one.
//!
//! [`fixture_matches_upstream_hol_mm`] is the real specification, and it needs
//! upstream hol.mm to state it: every `$a` in the fixture must have the same
//! conclusion, the same essential hypotheses and the same distinct-variable
//! conditions as its namesake in hol.mm, and no `$a` of hol.mm may be missing.
//! That is what makes the fixture an *extraction* rather than a transcription.
//! It is `#[ignore]`d for the same reason `corpus.rs` is: the corpus is a
//! multi-megabyte checkout we do not vendor.

use std::collections::BTreeMap;
use std::path::Path;

use covalence_logic_metamath::{
    Assertion, Database, FileResolver, Statement, parse, parse_with_resolver, verify_all,
};

const HOL_AX: &str = include_str!("fixtures/hol-ax.mm");

/// Every `$a` of hol.mm, in source order. Spelling out the list is the point:
/// "the axioms" was a judgement call — all 71 `$a`, meaning the 21 syntax
/// constructors (`tv` … `tat`) and the 11 `df-*` definitions as well as the 36
/// `ax-*` and the 3 mmj2 `wff` statements, for the reasons the fixture's own
/// header gives — and a judgement call should be visible in the test rather
/// than recomputed by it.
#[rustfmt::skip]
const AXIOMS: &[&str] = &[
    // syntax constructors for `var` / `type` / `term`
    "tv", "ht", "hb", "hi", "kc", "kl", "ke", "kt", "kbr", "kct",
    // mmj2 compatibility
    "wffMMJ2", "wffMMJ2t",
    // the logical axioms, with `df-ov` where hol.mm puts it
    "ax-syl", "ax-jca", "ax-simpl", "ax-simpr", "ax-id", "ax-trud", "ax-cb1",
    "ax-cb2", "ax-wctl", "ax-wctr", "ax-weq", "ax-refl", "ax-eqmp", "ax-ded",
    "ax-wct", "ax-wc", "ax-ceq", "ax-wv", "ax-wl", "ax-beta", "ax-distrc",
    "ax-leq", "ax-distrl", "ax-wov", "df-ov", "ax-eqtypi", "ax-eqtypri",
    "ax-hbl1", "ax-17", "ax-inst",
    // propositional constants and their definitions
    "tfal", "tan", "tne", "tim", "tal", "tex", "tor", "teu",
    "df-al", "df-fal", "df-an", "df-im", "df-not", "df-ex", "df-or", "df-eu",
    // the type-definition mechanism
    "wffMMJ2d", "ax-wabs", "ax-wrep", "ax-tdef",
    // extensionality
    "ax-eta",
    // infinity and choice
    "tf11", "tfo", "tat", "ax-wat", "df-f11", "df-fo", "ax-ac", "ax-inf",
];

fn fixture() -> Database {
    parse(HOL_AX).unwrap_or_else(|error| panic!("hol-ax.mm did not parse: {error}"))
}

/// Counts of each statement kind, keyed by the `.mm` keyword.
fn statement_census(db: &Database) -> BTreeMap<&'static str, usize> {
    let mut census = BTreeMap::new();
    for statement in db.statements() {
        let key = match statement {
            Statement::Constant(_) => "$c",
            Statement::Variable(_) => "$v",
            Statement::Float(_) => "$f",
            Statement::Essential(_) => "$e",
            Statement::Disjoint(_) => "$d",
            Statement::Assert(_) => "$a",
        };
        *census.entry(key).or_default() += 1;
    }
    census
}

/// `$d` pairs as an order-insensitive set: a `$d` is a symmetric relation on
/// variables, so `(x, y)` and `(y, x)` are the same condition, and the order
/// pairs are listed in carries no meaning.
fn disjoint_set(pairs: &[(String, String)]) -> Vec<(&str, &str)> {
    let mut set: Vec<(&str, &str)> = pairs
        .iter()
        .map(|(a, b)| {
            if a <= b {
                (a.as_str(), b.as_str())
            } else {
                (b.as_str(), a.as_str())
            }
        })
        .collect();
    set.sort_unstable();
    set.dedup();
    set
}

/// Label plus rendered math string for each essential hypothesis, in frame
/// order — the order is part of the assertion, since it is the order the
/// hypotheses are popped in when the axiom is applied.
fn essentials(assertion: &Assertion) -> Vec<(&str, String)> {
    assertion
        .frame
        .essentials
        .iter()
        .map(|h| (h.label.as_str(), h.expr.render()))
        .collect()
}

fn floats(assertion: &Assertion) -> Vec<(&str, &str, &str)> {
    assertion
        .frame
        .floats
        .iter()
        .map(|f| (f.label.as_str(), f.typecode.as_str(), f.var.as_str()))
        .collect()
}

/// Label, conclusion, essential hypotheses and mandatory `$d` for every
/// assertion — everything about a database that this fixture is meant to fix.
type Snapshot = Vec<(String, String, Vec<String>, Vec<(String, String)>)>;

fn snapshot(db: &Database) -> Snapshot {
    db.assertions()
        .map(|a| {
            (
                a.label.clone(),
                a.conclusion.render(),
                essentials(a).into_iter().map(|(_, e)| e).collect(),
                disjoint_set(&a.frame.disjoints)
                    .into_iter()
                    .map(|(x, y)| (x.to_owned(), y.to_owned()))
                    .collect(),
            )
        })
        .collect()
}

#[test]
fn fixture_is_an_axiom_only_database() {
    let db = fixture();

    let labels: Vec<&str> = db.assertions().map(|a| a.label.as_str()).collect();
    assert_eq!(labels, AXIOMS, "the fixture's axiom list changed");

    for assertion in db.assertions() {
        assert!(
            assertion.proof.is_none(),
            "{} carries a proof; this database is meant to hold none",
            assertion.label
        );
    }

    // No proofs means nothing to verify, and that is the expected outcome
    // rather than a degenerate one: `verify_all` reports how many `$p`
    // theorems it checked.
    assert_eq!(verify_all(&db).unwrap(), 0);
}

#[test]
fn fixture_keeps_the_scaffolding_the_axioms_need() {
    let db = fixture();

    // 31 constants, 6 variable declarations and 18 floating hypotheses: the
    // whole of hol.mm's declaration scaffolding, which no subset of it could
    // do without. 52 essential hypotheses and 13 `$d` statements: the ones
    // active where some axiom is stated. Nothing else is in the file.
    assert_eq!(
        statement_census(&db),
        BTreeMap::from([
            ("$c", 31),
            ("$v", 6),
            ("$f", 18),
            ("$e", 52),
            ("$d", 13),
            ("$a", 71),
        ])
    );

    // Every axiom's variables are typed — `build_frame` rejects a database
    // where they are not, so parsing at all already proved this; asserting it
    // says what the `$f` are *for*.
    for assertion in db.assertions() {
        for symbol in assertion.conclusion.symbols() {
            if db.is_variable(symbol) {
                assert!(
                    assertion.frame.floats.iter().any(|f| f.var == symbol),
                    "{} uses {symbol} with no floating hypothesis",
                    assertion.label
                );
            }
        }
    }

    // The `$d` conditions survived extraction. These four are the ones that do
    // real work — drop `$d x A` from ax-17 and it claims that substituting
    // into *any* term is the identity — so they are named here individually
    // rather than left to a count.
    let disjoints = |label: &str| {
        let Some(Statement::Assert(a)) = db.statement_by_label(label) else {
            panic!("{label} is not an assertion");
        };
        disjoint_set(&a.frame.disjoints)
    };
    assert_eq!(disjoints("ax-17"), [("A", "x")]);
    assert_eq!(disjoints("ax-leq"), [("R", "x")]);
    assert_eq!(disjoints("ax-distrl"), [("B", "y"), ("x", "y")]);
    assert_eq!(
        disjoints("ax-inst"),
        [("B", "y"), ("S", "y"), ("x", "y")],
        "ax-inst's three side conditions are what keep instantiation capture-free"
    );
}

#[test]
fn fixture_round_trips_through_the_emitter() {
    let db = fixture();
    let emitted = db.to_mm_string();
    let reparsed = parse(&emitted)
        .unwrap_or_else(|error| panic!("re-parse of the emitted database failed: {error}"));
    assert_eq!(snapshot(&db), snapshot(&reparsed));
}

#[test]
#[ignore = "requires NUCLEUS_METAMATH_CORPUS=/path/to/metamath/set.mm checkout"]
fn fixture_matches_upstream_hol_mm() {
    let root = std::env::var("NUCLEUS_METAMATH_CORPUS")
        .expect("set NUCLEUS_METAMATH_CORPUS to a checkout of metamath/set.mm");
    assert!(
        Path::new(&root).join("hol.mm").is_file(),
        "missing hol.mm in {root}"
    );
    let upstream = parse_with_resolver("hol.mm", &FileResolver::new(&root))
        .unwrap_or_else(|error| panic!("hol.mm did not parse: {error}"));
    let db = fixture();

    // Which assertions are axioms is upstream's call, not ours: an axiom is a
    // `$a`, which the parser records as an assertion with no proof.
    let upstream_axioms: BTreeMap<&str, &Assertion> = upstream
        .assertions()
        .filter(|a| a.proof.is_none())
        .map(|a| (a.label.as_str(), a))
        .collect();
    let extracted: BTreeMap<&str, &Assertion> =
        db.assertions().map(|a| (a.label.as_str(), a)).collect();

    assert_eq!(
        upstream_axioms.keys().collect::<Vec<_>>(),
        extracted.keys().collect::<Vec<_>>(),
        "the extracted axiom set differs from hol.mm's"
    );

    for (label, ours) in &extracted {
        let theirs = upstream_axioms[label];

        // The conclusion compares as a typecode plus a symbol sequence, which
        // is exactly what a Metamath math string is: equal here means the
        // statement was copied, not restated.
        assert_eq!(
            ours.conclusion,
            theirs.conclusion,
            "{label}: conclusion differs\n  ours:   {}\n  theirs: {}",
            ours.conclusion.render(),
            theirs.conclusion.render()
        );
        assert_eq!(
            essentials(ours),
            essentials(theirs),
            "{label}: essential hypotheses differ"
        );
        assert_eq!(
            floats(ours),
            floats(theirs),
            "{label}: $f signature differs"
        );
        assert_eq!(
            disjoint_set(&ours.frame.disjoints),
            disjoint_set(&theirs.frame.disjoints),
            "{label}: mandatory $d conditions differ"
        );
        // `scope_disjoints` is the unfiltered set active where the axiom is
        // stated, including pairs over variables the axiom does not mention.
        // Those never constrain a `$a`, but a mismatch would mean the
        // extraction moved a statement across a `$d`, so it is worth catching.
        assert_eq!(
            disjoint_set(&ours.scope_disjoints),
            disjoint_set(&theirs.scope_disjoints),
            "{label}: in-scope $d conditions differ"
        );
    }
}

#[test]
#[ignore = "requires NUCLEUS_METAMATH_CORPUS=/path/to/metamath/set.mm checkout"]
fn fixture_body_is_copied_verbatim_from_hol_mm() {
    let root = std::env::var("NUCLEUS_METAMATH_CORPUS")
        .expect("set NUCLEUS_METAMATH_CORPUS to a checkout of metamath/set.mm");
    let upstream = std::fs::read_to_string(Path::new(&root).join("hol.mm")).unwrap();
    let upstream_lines: std::collections::HashSet<&str> = upstream.lines().collect();

    // Everything after the generated header is upstream text, copied line by
    // line — statements and their documentation alike. This is the crude
    // check that complements the structural one: it catches a reflowed comment
    // or a retyped math string that happens to parse the same, and it is the
    // reason the fixture can claim to preserve hol.mm's prose rather than
    // paraphrase it.
    let body = HOL_AX
        .lines()
        .skip_while(|line| !line.starts_with("$( !"))
        .filter(|line| !line.trim().is_empty());
    let mut checked = 0usize;
    for line in body {
        assert!(
            upstream_lines.contains(line),
            "line is not verbatim from hol.mm: {line:?}"
        );
        checked += 1;
    }
    assert!(checked > 400, "expected the whole body, checked {checked}");
}
