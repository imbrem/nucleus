//! A canonical `.mm` **emitter**: render a [`Database`] back to valid Metamath
//! source that re-parses to a structurally-equivalent database.
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
//! Metamath's own scoping convention is: `$c`/`$v`/`$f` are (conventionally)
//! *global*, while `$e`/`$d` are *scoped* to the assertion(s) that need them.
//! The emitter mirrors that, and crucially **preserves the original `$f`/`$e`
//! labels** so that normal proofs — which cite `$f`/`$e` labels by name — keep
//! resolving:
//!
//! 1. Emit all `$c` then all `$v` declarations (source order).
//! 2. Emit every `$f` floating hypothesis **globally**, once per label, with its
//!    original label. Floats are the "type signatures" proofs reference by name.
//! 3. Emit each assertion inside its own `${ ... $}` block containing exactly its
//!    mandatory `$e` essentials (in order) and its mandatory `$d` pairs, then the
//!    `$a`/`$p`. Because `build_frame` recomputes the mandatory frame from the
//!    active scope, and the globals + the block's `$e`/`$d` reproduce that frame
//!    exactly, re-parsing yields an assertion with the **identical** frame — with
//!    no dependence on recovering the original scope nesting.
//!
//! Assertion labels and `$f` labels are preserved verbatim. A `$e` essential
//! **shared** by several assertions in one original `${ $}` (e.g. `hol.mm`'s
//! `ax-syl.1`, used by both `ax-syl` and `syl`) cannot keep one global label —
//! each self-contained block would re-declare it and collide — so each block's
//! essentials are **re-labelled uniquely** (`<assertion>__<orig>`). A theorem's
//! own [`Proof::Normal`] label references to its essentials are rewritten to
//! match; [`Proof::Compressed`] proofs address mandatory hypotheses *positionally*
//! (never by label), so they are unaffected.
//!
//! ## Proofs
//!
//! [`Proof::Normal`] renders as its RPN label sequence. [`Proof::Compressed`]
//! renders as `( labels ) LETTERS` — the compressed form is emitted verbatim
//! (the label block + letter block round-trip losslessly through the parser).
//! A compressed proof's letter block addresses *mandatory hypotheses by frame
//! position*, so it stays valid as long as the emitted frame order matches the
//! original — which it does (globals give the floats in database order, the
//! block gives the essentials in order).
//!
//! ## Limitations
//!
//! * **Global `$f` only.** A *scoped* `$f` that retypes the same variable
//!   differently in two scopes is flattened to one global typing. Databases we
//!   handle (demo0, `set.mm`-style) declare `$f` globally, so this is faithful in
//!   practice; a database that relies on re-typing scoped floats is not
//!   round-tripped. (Emitting such a `$f` twice with the same label would be a
//!   duplicate-label error; different labels would break proof references — so
//!   this is a genuine limitation, not a silent bug.)
//! * **Essential re-labelling is not collision-checked.** Each block's `$e` is
//!   re-labelled `<assertion>__<orig>`, and nothing verifies that name is free:
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
/// [`parse`](crate::parse())) to a database with the same symbols and the same assertion
/// statements (labels, conclusions, and mandatory frames). See the module docs
/// for the normalisation performed.
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

    // 2. Global floating hypotheses, one per label (original labels preserved so
    //    proofs that cite them still resolve). A given label appears once in the
    //    statement list, so dedup-by-label is just a guard.
    let mut seen: HashSet<&str> = HashSet::new();
    for stmt in db.statements() {
        if let Statement::Float(f) = stmt
            && seen.insert(f.label.as_str())
        {
            let _ = writeln!(out, "{} $f {} {} $.", f.label, f.typecode, f.var);
        }
    }
    out.push('\n');

    // 3. Each assertion in its own scoped block (its essentials + $d, then the
    //    $a/$p). Floats are already global.
    for a in db.assertions() {
        emit_assertion(&mut out, a);
    }

    out
}

/// Emit one assertion as `${ <essentials> <disjoints> <assert> $}`, or bare when
/// it has neither essentials nor `$d` (its floats are global, so nothing needs
/// scoping). Essential labels are re-labelled block-uniquely so a `$e` shared by
/// several assertions in the original source does not collide across blocks; a
/// normal proof's references to this assertion's own essentials are rewritten.
fn emit_assertion(out: &mut String, a: &Assertion) {
    // The full in-scope `$d` set (`scope_disjoints`) is what a `$p` proof is
    // *checked against* — it may mention dummy/working variables beyond the
    // mandatory frame. Emitting it (rather than just `frame.disjoints`) keeps
    // proofs valid; `build_frame` re-filters to the mandatory subset on re-parse,
    // so `frame.disjoints` is reproduced too.
    let dd = dedup_pairs(&a.scope_disjoints);
    let needs_scope = !a.frame.essentials.is_empty() || !dd.is_empty();

    if needs_scope {
        out.push_str("${\n");
    }

    // Block-unique essential labels: `<assertion>__<orig>`. Underscores keep the
    // label a valid Metamath token and make the provenance readable.
    let mut ess_rename: std::collections::HashMap<&str, String> = std::collections::HashMap::new();
    for h in &a.frame.essentials {
        let new_label = format!("{}__{}", a.label, h.label);
        let _ = writeln!(out, "  {} $e {} $.", new_label, h.expr.render());
        ess_rename.insert(h.label.as_str(), new_label);
    }
    // Disjoint-variable conditions (one $d per pair; the parser expands pairs).
    for (x, y) in &dd {
        let _ = writeln!(out, "  $d {x} {y} $.");
    }

    let indent = if needs_scope { "  " } else { "" };
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
                    ess_rename
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
            // Compressed proofs address mandatory hyps positionally, so the
            // essential re-labelling never appears in the label block.
            let _ = writeln!(
                out,
                "{indent}{} $p {concl} $= ( {} ) {} $.",
                a.label,
                labels.join(" "),
                String::from_utf8_lossy(letters),
            );
        }
    }

    if needs_scope {
        out.push_str("$}\n");
    }
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
        // Frames are byte-identical here: floats keep their original labels.
        assert_eq!(a1.frame, a2.frame);
        assert_eq!(a2.frame.disjoints.len(), 1);
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

    fn assert_of<'a>(db: &'a Database, label: &str) -> &'a Assertion {
        match db.statement_by_label(label).unwrap() {
            Statement::Assert(a) => a,
            _ => unreachable!(),
        }
    }
}
