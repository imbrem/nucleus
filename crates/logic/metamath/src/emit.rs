//! A canonical `.mm` **emitter**: render a [`Database`] back to valid Metamath
//! source that re-parses to a semantically-equivalent database.
//!
//! ## Why not just replay the statement list verbatim?
//!
//! A parsed [`Database`] keeps its statements in source order but **does not**
//! retain the `${ ... $}` scope markers (they leave no [`Statement`]). A naive
//! "print each statement in order" therefore cannot know which `$e`/`$d` were
//! scoped, and re-parsing would leak those scoped hypotheses into later
//! assertions — changing their frames.
//!
//! ## The strategy
//!
//! The emitter gives every assertion a self-contained scope containing its
//! complete active `$f` context, mandatory `$e` context, and active `$d`
//! context:
//!
//! 1. Emit all `$c` then all `$v` declarations (source order).
//! 2. Emit each assertion inside its own `${ ... $}` block containing all of its
//!    active `$f`, `$e`, and `$d` data, then the `$a`/`$p`.
//!
//! Hypotheses shared by multiple original assertions are re-labelled uniquely
//! (`<assertion>__<orig>`) in each self-contained block. Normal proof references
//! are rewritten to match. Compressed proofs address mandatory hypotheses
//! positionally and are unaffected.
//!
//! ## Proofs
//!
//! [`Proof::Normal`] renders as its RPN label sequence. [`Proof::Compressed`]
//! renders as `( labels ) LETTERS`; its letters are preserved and any active
//! hypothesis in its explicit label block follows the block-local rename.
//! A compressed proof's letter block addresses *mandatory hypotheses by frame
//! position*, so it stays valid because each block preserves float and
//! essential order.
//!
//! ## Limitations
//!
//! * **Hypothesis re-labelling is not collision-checked.** Each block's `$f` and
//!   `$e` labels are prefixed with the assertion label, and nothing verifies
//!   that name is free:
//!   a source database already containing a label of exactly that shape (say an
//!   assertion `th` with essential `h`, alongside an unrelated `th__h`) would
//!   have the generated label clash with it. The clash is loud rather than
//!   silent — the emitted source fails to re-parse with a duplicate-label error,
//!   so no wrong database is produced — but the emitter cannot currently emit
//!   such a database at all.
//! * **No comment/`$[ $]` preservation.** The output is a *normalised* database,
//!   equivalent under re-parse but not byte-identical to the original source.

use std::collections::HashSet;
use std::fmt::Write;

use crate::database::{Assertion, Database, Proof, Statement};

/// Render `db` to canonical `.mm` source. The result re-parses (via
/// [`parse`](crate::parse())) to a database with the same symbols and assertion
/// semantics. Hypothesis labels are normalized. See the module docs for the
/// normalization performed.
#[must_use]
pub fn to_mm_string(db: &Database) -> String {
    let mut out = String::new();

    // 1. Global constant / variable declarations, in source order.
    for stmt in db.statements() {
        match stmt {
            Statement::Constant(syms) => {
                let _ = writeln!(out, "$c {} $.", syms.join(" "));
            }
            Statement::Variable(syms) => {
                let _ = writeln!(out, "$v {} $.", syms.join(" "));
            }
            _ => {}
        }
    }
    out.push('\n');

    // 2. Each assertion gets a self-contained active context.
    for a in db.assertions() {
        emit_assertion(&mut out, a);
    }

    out
}

/// Emit one assertion with a self-contained active context. Hypothesis labels
/// are block-unique, and normal proof references are rewritten accordingly.
fn emit_assertion(out: &mut String, a: &Assertion) {
    // The full in-scope `$d` set (`scope_disjoints`) is what a `$p` proof is
    // *checked against* — it may mention dummy/working variables beyond the
    // mandatory frame. Emitting it (rather than just `frame.disjoints`) keeps
    // proofs valid; `build_frame` re-filters to the mandatory subset on re-parse,
    // so `frame.disjoints` is reproduced too.
    let dd = dedup_pairs(&a.scope_disjoints);
    out.push_str("${\n");

    // Block-unique hypothesis labels. Underscores keep the
    // label a valid Metamath token and make the provenance readable.
    let mut hyp_rename: std::collections::HashMap<&str, String> = std::collections::HashMap::new();
    for f in &a.scope_floats {
        let new_label = format!("{}__{}", a.label, f.label);
        let _ = writeln!(out, "  {new_label} $f {} {} $.", f.typecode, f.var);
        hyp_rename.insert(f.label.as_str(), new_label);
    }
    for h in &a.frame.essentials {
        let new_label = format!("{}__{}", a.label, h.label);
        let _ = writeln!(out, "  {} $e {} $.", new_label, h.expr.render());
        hyp_rename.insert(h.label.as_str(), new_label);
    }
    // Disjoint-variable conditions (one $d per pair; the parser expands pairs).
    for (x, y) in &dd {
        let _ = writeln!(out, "  $d {x} {y} $.");
    }

    let indent = "  ";
    let concl = a.conclusion.render();
    match &a.proof {
        None => {
            let _ = writeln!(out, "{indent}{} $a {concl} $.", a.label);
        }
        Some(Proof::Normal(labels)) => {
            // Rewrite references to this assertion's own (re-labelled) essentials.
            let steps: Vec<&str> = labels
                .iter()
                .map(|l| {
                    hyp_rename
                        .get(l.as_str())
                        .map_or(l.as_str(), String::as_str)
                })
                .collect();
            let _ = writeln!(
                out,
                "{indent}{} $p {concl} $= {} $.",
                a.label,
                steps.join(" ")
            );
        }
        Some(Proof::Compressed { labels, letters }) => {
            // Mandatory hypotheses are positional, but active non-mandatory
            // floats occur in the explicit label block and must follow the
            // block-local rename.
            let labels: Vec<&str> = labels
                .iter()
                .map(|label| {
                    hyp_rename
                        .get(label.as_str())
                        .map_or(label.as_str(), String::as_str)
                })
                .collect();
            let _ = writeln!(
                out,
                "{indent}{} $p {concl} $= ( {} ) {} $.",
                a.label,
                labels.join(" "),
                String::from_utf8_lossy(letters),
            );
        }
    }

    out.push_str("$}\n");
}

/// Deduplicate `$d` pairs (unordered), dropping any degenerate `(x, x)`.
fn dedup_pairs(pairs: &[(String, String)]) -> Vec<(String, String)> {
    // `seen` borrows from `pairs`, so the membership test costs nothing: only a
    // pair that survives deduplication is ever cloned.
    let mut seen: HashSet<(&str, &str)> = HashSet::new();
    let mut out = Vec::new();
    for (x, y) in pairs {
        if x == y {
            continue;
        }
        let key = if x <= y {
            (x.as_str(), y.as_str())
        } else {
            (y.as_str(), x.as_str())
        };
        if seen.insert(key) {
            out.push((key.0.to_owned(), key.1.to_owned()));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    const DEMO0: &str = include_str!("../tests/fixtures/demo0.mm");

    /// Label, conclusion, essential expressions, and float signature of every
    /// assertion — enough to say two databases agree without comparing scopes.
    type Snapshot = Vec<(String, String, Vec<String>, Vec<(String, String)>)>;

    fn assertions_snapshot(db: &Database) -> Snapshot {
        let mut v: Vec<_> = db
            .assertions()
            .map(|a| {
                (
                    a.label.clone(),
                    a.conclusion.render(),
                    a.frame.essentials.iter().map(|h| h.expr.render()).collect(),
                    a.frame
                        .floats
                        .iter()
                        .map(|f| (f.typecode.clone(), f.var.clone()))
                        .collect(),
                )
            })
            .collect();
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    }

    #[test]
    fn demo0_round_trips_through_emitter() {
        let db1 = parse(DEMO0).unwrap();
        let emitted = to_mm_string(&db1);
        let db2 =
            parse(&emitted).unwrap_or_else(|e| panic!("re-parse failed: {e}\n---\n{emitted}"));
        assert_eq!(assertions_snapshot(&db1), assertions_snapshot(&db2));
        // The re-emitted database also re-verifies: proofs cite $f/$e/assertion
        // labels, all preserved; the frame order (globals give floats in database
        // order, blocks give essentials in order) is preserved too.
        assert_eq!(crate::verify_all(&db1).unwrap(), 1);
        assert_eq!(crate::verify_all(&db2).unwrap(), 1);
    }

    #[test]
    fn round_trips_scoped_disjoints() {
        // An assertion whose mandatory frame carries a $d must round-trip that
        // $d (a scoped $d the flat statement list cannot otherwise recover).
        let src = "$c wff |- ( ) -> $.\n$v ph ps $.\n\
                   wph $f wff ph $.\nwps $f wff ps $.\n\
                   ${ $d ph ps $.  ax $a |- ( ph -> ps ) $. $}\n";
        let db1 = parse(src).unwrap();
        let db2 = parse(&to_mm_string(&db1)).unwrap();
        let a1 = assert_of(&db1, "ax");
        let a2 = assert_of(&db2, "ax");
        assert_eq!(
            a1.frame
                .floats
                .iter()
                .map(|f| (&f.typecode, &f.var))
                .collect::<Vec<_>>(),
            a2.frame
                .floats
                .iter()
                .map(|f| (&f.typecode, &f.var))
                .collect::<Vec<_>>()
        );
        assert_eq!(a1.frame.disjoints, a2.frame.disjoints);
        assert_eq!(a2.frame.disjoints.len(), 1);
    }

    #[test]
    fn round_trips_scoped_float_contexts_without_leaking() {
        let src = "$c wff |- $.\n$v ph $.\n\
                   ${ first $f wff ph $. a $a |- ph $. $}\n\
                   ${ second $f wff ph $. b $a |- ph $. $}\n";
        let db1 = parse(src).unwrap();
        let db2 = parse(&to_mm_string(&db1)).unwrap();
        for label in ["a", "b"] {
            let before = assert_of(&db1, label);
            let after = assert_of(&db2, label);
            assert_eq!(before.scope_floats.len(), 1);
            assert_eq!(after.scope_floats.len(), 1);
            assert_eq!(
                before.scope_floats[0].typecode,
                after.scope_floats[0].typecode
            );
            assert_eq!(before.scope_floats[0].var, after.scope_floats[0].var);
        }
    }

    #[test]
    fn round_trips_essentials_dont_leak() {
        // Two assertions where the first has an essential; re-parse must NOT
        // attach that essential to the second (the scope-leak hazard).
        let src = "$c wff |- ( ) -> $.\n$v ph ps $.\n\
                   wph $f wff ph $.\nwps $f wff ps $.\n\
                   wi $a wff ( ph -> ps ) $.\n\
                   ${ h $e |- ph $.  m $a |- ps $. $}\n\
                   free $a |- ph $.\n";
        let db1 = parse(src).unwrap();
        let db2 = parse(&to_mm_string(&db1)).unwrap();
        assert!(
            assert_of(&db2, "free").frame.essentials.is_empty(),
            "the scoped essential must not leak into `free`"
        );
        // And `m` still has exactly its one essential.
        assert_eq!(assert_of(&db2, "m").frame.essentials.len(), 1);
    }

    #[test]
    fn compressed_proof_round_trips() {
        // A compressed-proof theorem's `( labels ) LETTERS` form re-parses to an
        // equal Proof::Compressed.
        let src = "$c wff |- ( ) -> $.\n$v ph ps $.\n\
                   wph $f wff ph $.\nwps $f wff ps $.\n\
                   wi $a wff ( ph -> ps ) $.\n\
                   ${ min $e |- ph $. maj $e |- ( ph -> ps ) $. mp $a |- ps $. $}\n\
                   id $p |- ( ph -> ph ) $= ( ) A $.\n";
        let db1 = parse(src).unwrap();
        let db2 = parse(&to_mm_string(&db1)).unwrap();
        assert_eq!(assertions_snapshot(&db1), assertions_snapshot(&db2));
        // The compressed encoding survived as-is.
        assert_eq!(assert_of(&db1, "id").proof, assert_of(&db2, "id").proof);
    }

    #[test]
    fn compressed_dummy_float_round_trips() {
        let src = "$c term |- $.\n$v x y $.\n\
                   tx $f term x $. ty $f term y $.\n\
                   ${ h $e term y $. ax $a |- x $. $}\n\
                   th $p |- x $= ( ty ax ) ABBC $.\n";
        let db1 = parse(src).unwrap();
        assert_eq!(crate::verify_all(&db1).unwrap(), 1);
        let emitted = to_mm_string(&db1);
        let db2 = parse(&emitted).unwrap();
        assert_eq!(crate::verify_all(&db2).unwrap(), 1);
        assert!(emitted.contains("( th__ty ax )"), "{emitted}");
    }

    fn assert_of<'a>(db: &'a Database, label: &str) -> &'a Assertion {
        match db.statement_by_label(label).unwrap() {
            Statement::Assert(a) => a,
            _ => unreachable!(),
        }
    }
}
