//! Regression tests for the checker's *scope* and *ordering* discipline.
//!
//! Everything here is a database that parses cleanly and whose proofs are
//! individually well-formed RPN — the only thing wrong with them is *where*
//! they take their premises from. A read-as-you-go verifier gets these right
//! for free, because its label table is the prefix of the file already read;
//! this crate parses first and checks afterwards, so each has to be rejected
//! explicitly. Every one of the rejected databases below "proves" `|- ph` for
//! an arbitrary `ph`, i.e. proves everything.
//!
//! The accepted cases are the other half of the contract: citing an earlier
//! theorem, and citing one's own `$e` premises, are the ordinary way proofs are
//! written and must keep working.

use covalence_logic_metamath::{MmError, parse, verify_all};

/// Propositional preamble shared by the fixtures: a `wff` variable `ph`, its
/// floating hypothesis, and modus-ponens-shaped machinery where needed.
const PREAMBLE: &str = "\
    $c wff |- $.\n\
    $v ph ps $.\n\
    wph $f wff ph $.\n\
    wps $f wff ps $.\n\
";

fn database(body: &str) -> String {
    format!("{PREAMBLE}{body}")
}

// --- ordering: a theorem may not cite itself or anything later --------------

#[test]
fn theorem_may_not_prove_itself() {
    let input = database("a $p |- ph $= wph a $.\n");
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::ForwardReference { theorem, label }
            if theorem == "a" && label == "a"),
        "{error}"
    );
}

#[test]
fn two_theorems_may_not_prove_each_other() {
    let input = database(
        "a $p |- ph $= wph b $.\n\
         b $p |- ph $= wph a $.\n",
    );
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::ForwardReference { theorem, label }
            if theorem == "a" && label == "b"),
        "{error}"
    );
}

#[test]
fn a_theorem_may_not_cite_a_later_axiom() {
    // Not circular — just out of order. Metamath's reading order forbids it,
    // and permitting it is what makes the circular cases above possible.
    let input = database(
        "th $p |- ph $= wph ax $.\n\
         ax $a |- ph $.\n",
    );
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::ForwardReference { theorem, label }
            if theorem == "th" && label == "ax"),
        "{error}"
    );
}

#[test]
fn self_reference_in_a_compressed_proof_is_rejected() {
    // The label block resolves fine; the *citation* is the problem, so the
    // rejection has to happen on the decoded step, not at decode time.
    let input = database("a $p |- ph $= ( a ) AB $.\n");
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::ForwardReference { theorem, label }
            if theorem == "a" && label == "a"),
        "{error}"
    );
}

// --- scope: a theorem may not cite another block's `$e` --------------------

#[test]
fn a_proof_may_not_cite_an_out_of_scope_essential() {
    // `h1` is declared earlier than `bad`, so ordering alone does not catch
    // this: it is out of *scope*, not out of order.
    let input = database(
        "${\n\
           h1 $e |- ph $.\n\
           mp $a |- ph $.\n\
         $}\n\
         bad $p |- ph $= h1 $.\n",
    );
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::InactiveHypothesis { theorem, label }
            if theorem == "bad" && label == "h1"),
        "{error}"
    );
}

#[test]
fn a_proof_may_not_cite_a_sibling_block_essential() {
    // Both blocks are closed before `bad` opens, and `bad` has an essential of
    // its own — so the frame is non-empty and the wrong premise still has to be
    // rejected on identity, not on emptiness.
    let input = database(
        "${\n\
           other $e |- ps $.\n\
           lem $a |- ps $.\n\
         $}\n\
         ${\n\
           mine $e |- ph $.\n\
           bad $p |- ps $= other $.\n\
         $}\n",
    );
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::InactiveHypothesis { theorem, label }
            if theorem == "bad" && label == "other"),
        "{error}"
    );
}

// --- the normal cases, which must keep verifying ---------------------------

/// The "demo0" database from the Metamath book: a self-contained proof that
/// exercises floats, an axiom with essentials, and nested applications.
const DEMO0: &str = "\
    $c 0 + = -> ( ) term wff |- $.\n\
    $v t r s P Q $.\n\
    tt $f term t $.\n\
    tr $f term r $.\n\
    ts $f term s $.\n\
    wp $f wff P $.\n\
    wq $f wff Q $.\n\
    tze $a term 0 $.\n\
    tpl $a term ( t + r ) $.\n\
    weq $a wff t = r $.\n\
    wim $a wff ( P -> Q ) $.\n\
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
    a2 $a |- ( t + 0 ) = t $.\n\
    ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
        mp $a |- Q $.\n\
    $}\n\
    th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
        tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
        tt tt a1 mp mp $.\n\
";

#[test]
fn a_legitimate_proof_still_verifies() {
    let db = parse(DEMO0).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

#[test]
fn a_proof_citing_an_earlier_theorem_still_verifies() {
    // The ordinary case the ordering check must not break: `th2` is proved by
    // applying `th1`, which precedes it.
    let input = format!("{DEMO0}th2 $p |- 0 = 0 $= tze th1 $.\n");
    let db = parse(&input).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 2);
}

#[test]
fn a_proof_citing_its_own_essentials_still_verifies() {
    let input = database(
        "${\n\
           maj $e |- ph $.\n\
           th $p |- ph $= maj $.\n\
         $}\n",
    );
    let db = parse(&input).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

#[test]
fn a_proof_citing_a_non_mandatory_float_still_verifies() {
    // A dummy (working) variable: `ps` appears nowhere in `th`'s statement, so
    // `wps` is active but *not* in `th`'s mandatory frame. `set.mm` cites
    // non-mandatory floats around 200 000 times, so the scope check must not be
    // a mandatory-frame test for `$f`.
    let input = database(
        "drop $a |- ph $.\n\
         ${\n\
           min $e |- ps $.\n\
           use $a |- ph $.\n\
         $}\n\
         th $p |- ph $= wph wps wps drop use $.\n",
    );
    let db = parse(&input).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
}

// --- compressed proof integers: untrusted input may not overflow -----------

#[test]
fn an_overflowing_proof_integer_is_an_error_not_a_panic() {
    // ~80 continuation digits then a terminal one: `n * 5 + d` runs off the end
    // of a `usize`. In debug that used to panic; in release it wrapped onto a
    // small, and therefore *addressable*, proof step.
    let letters = format!("{}A", "U".repeat(80));
    let input = database(&format!("th $p |- ph $= ( wph ) {letters} $.\n"));
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::CompressedProofError { theorem, .. } if theorem == "th"),
        "{error}"
    );
}

#[test]
fn a_proof_integer_at_the_edge_of_usize_is_an_error_not_a_wrap() {
    // Long enough to overflow but not by orders of magnitude, so a wrapped
    // value would land in the low, valid range rather than obviously far away.
    let letters = format!("{}T", "Y".repeat(28));
    let input = database(&format!("th $p |- ph $= ( wph ) {letters} $.\n"));
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    assert!(
        matches!(&error, MmError::CompressedProofError { theorem, .. } if theorem == "th"),
        "{error}"
    );
}

#[test]
fn a_long_but_representable_proof_integer_is_still_decoded() {
    // The overflow guard must not clip legitimately large addresses: this one
    // is far past the end of the proof, so it is rejected as out of range —
    // by the heap check, not by the arithmetic.
    let letters = "UUUUUUUUUUA";
    let input = database(&format!("th $p |- ph $= ( wph ) {letters} $.\n"));
    let db = parse(&input).unwrap();
    let error = verify_all(&db).unwrap_err();
    let MmError::CompressedProofError { theorem, message } = &error else {
        panic!("{error}");
    };
    assert_eq!(theorem, "th");
    assert!(message.contains("heap backreference"), "{message}");
}
