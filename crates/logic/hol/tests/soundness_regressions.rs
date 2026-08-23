//! Regression tests for kernel rules that used to mint facts the semantics
//! does not justify.
//!
//! Each test names the issue it guards. They are deliberately phrased as
//! derivations a caller could actually run, not as unit tests of an internal
//! predicate, so that a future refactor cannot satisfy them vacuously.

mod support;

use covalence_logic_cas::CasFact;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, SynRel, Table, wire};
use support::{ArenaCbor, Fix, Prover};

fn invalid(error: &KernelError) -> &'static str {
    match error {
        KernelError::InvalidSynFact { rule } => rule,
        other => panic!("expected a rejected local rule, got {other:?}"),
    }
}

/// `y : model 9 x` — a term variable whose *type* mentions the term variable
/// `x`. `ty.model` embeds a term in a type, so this is ordinary Ethane syntax
/// and `[true / x]` has to rewrite the annotation along with everything else.
struct Guarded {
    fix: Fix,
    /// The term variable being substituted for.
    subject: Ref,
    /// The replacement for `subject`.
    value: Ref,
    /// `model 9 x`.
    guard: Ref,
    /// `y : model 9 x`.
    annotated: Ref,
}

fn guarded() -> Guarded {
    let mut fix = Fix::new();
    let subject = fix.var(0);
    let value = fix.lit(true);
    let guard = fix.model(9, subject).expect("model 9 x");
    let annotated = fix.tm_fv(1, guard).expect("y : model 9 x");
    Guarded {
        fix,
        subject,
        value,
        guard,
        annotated,
    }
}

#[test]
fn a_leaf_may_not_ignore_an_annotation_that_mentions_the_substituted_variable() {
    // A different variable name is not enough to make a `tm.fv` row invariant:
    // `[true / x] (y : model 9 x)` is `y : model 9 true`, a different row.
    let Guarded {
        mut fix,
        subject,
        value,
        annotated,
        ..
    } = guarded();

    let error = fix
        .syn_sub_leaf(None, subject, value, annotated)
        .expect_err("the annotation mentions `x`");
    assert_eq!(invalid(&error), "substitution leaf");
}

#[test]
fn the_bad_leaf_no_longer_composes_into_a_beta_conversion() {
    // The end-to-end shape the gap allowed: a closed Boolean redex whose
    // reduct kept a guard mentioning the variable that had just been replaced.
    let Guarded {
        mut fix,
        subject,
        value,
        annotated,
        guard: _,
    } = guarded();
    let bool_ty = fix.bool_ty;

    let body = fix.eq(bool_ty, annotated, annotated).expect("y = y : bool");
    let function = fix.lam(subject, body).expect("λx. (y = y)");
    let redex = fix.app(function, value).expect("(λx. y = y) true");

    assert!(fix.syn_sub_leaf(None, subject, value, annotated).is_err());
    // Congruence is the only remaining route, and it demands a fact for the
    // annotation, which is exactly the obligation the leaf rule was skipping.
    let guard = fix.classifier(annotated).expect("annotation");
    let reflexive_guard = fix.syn_refl(None, SynRel::Syn, guard).expect("reflexivity");
    assert!(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            annotated,
            annotated,
            &[reflexive_guard],
        )
        .is_err()
    );
    assert!(!fix.tm_eq(redex, body).expect("resident"));
}

#[test]
fn a_leaf_is_still_unchanged_when_the_annotation_cannot_mention_the_variable() {
    // The fix must not cost the ordinary case: a `bool`-typed variable is
    // invariant under any substitution for a differently named variable.
    let mut fix = Fix::new();
    let subject = fix.var(0);
    let value = fix.lit(true);
    let other = fix.var(1);
    let arrow = fix.bool_arrow();
    let function = fix.tm_fv(2, arrow).expect("function variable");

    for leaf in [other, function] {
        assert!(
            fix.syn_sub_leaf(None, subject, value, leaf).is_ok(),
            "{leaf:?} cannot mention `x`"
        );
    }

    // A type variable's classifier is a kind, and kinds hold no named syntax,
    // so a type variable is invariant under a term substitution too.
    let alpha = fix.ty_var(3);
    assert!(fix.syn_sub_leaf(None, subject, value, alpha).is_ok());
}

#[test]
fn a_type_replacement_reaches_a_term_variable_exactly_when_it_has_to() {
    let mut fix = Fix::new();
    let star = fix.star;
    let alpha = fix.ty_fv(1, star).expect("type variable");
    let beta = fix.ty_fv(2, star).expect("type variable");

    // `z : α` is not invariant under `[β / α]`.
    let at_alpha = fix.tm_fv(3, alpha).expect("z : α");
    let error = fix
        .syn_sub_leaf(None, alpha, beta, at_alpha)
        .expect_err("the annotation is `α` itself");
    assert_eq!(invalid(&error), "substitution leaf");

    // `z : bool` is.
    let at_bool = fix.var(3);
    assert!(fix.syn_sub_leaf(None, alpha, beta, at_bool).is_ok());
}

#[test]
fn binder_congruence_may_not_carry_an_annotation_the_substitution_rewrites() {
    // `syn_binder_congr` passes the binder row through untouched for a term
    // substitution, so the binder's own type must be out of the substitution's
    // reach. `λ(y : model 9 x). z` under `[true / x]` is not.
    let Guarded {
        mut fix,
        subject,
        value,
        guard,
        annotated,
    } = guarded();
    let bool_ty = fix.bool_ty;
    let free = fix.var(2);

    let input = fix.lam(annotated, free).expect("λ(y : model 9 x). z");
    let arrow = fix.classifier(input).expect("function type");
    let leaf = fix
        .syn_sub_leaf(None, subject, value, free)
        .expect("`z : bool` cannot mention `x`");
    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, annotated)
        .expect("reflexivity");

    let error = fix
        .syn_binder_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            input,
            input,
            binder_fact,
            leaf,
        )
        .expect_err("the binder's type mentions `x`");
    assert_eq!(invalid(&error), "binder classifier");
    let _ = (guard, arrow, bool_ty);
}

#[test]
fn binder_congruence_still_works_when_the_binder_is_out_of_reach() {
    let mut fix = Fix::new();
    let arrow = fix.bool_arrow();
    let binder = fix.var(0);
    let free = fix.var(1);
    let value = fix.lit(true);

    let input = fix.lam(binder, free).expect("λy. z");
    let output = fix.lam(binder, value).expect("λy. true");
    let minted = fix.classifier(input).expect("function type");
    let other = fix.classifier(output).expect("function type");
    let prover = fix.prover();
    prover
        .union_equal(&mut fix.kernel, minted, other)
        .expect("merge the duplicate arrows");
    prover
        .union_equal(&mut fix.kernel, minted, arrow)
        .expect("merge the duplicate arrows");

    let binder_fact = fix
        .syn_refl(None, SynRel::Syn, binder)
        .expect("reflexivity");
    let body_fact = fix.syn_sub_var(None, free, value).expect("sub var");
    assert!(
        fix.syn_binder_congr(
            None,
            SynRel::Syn,
            Some(free),
            Some(value),
            input,
            output,
            binder_fact,
            body_fact,
        )
        .is_ok(),
        "a `bool` binder is untouched by a substitution for another variable"
    );
}

/// `λv. f v` over a type built by `depth` doublings of `bool`, with the
/// abstraction's freshly minted arrow merged into `f`'s type class.
fn eta_at_depth(depth: u32) -> Result<SynFactId, KernelError> {
    let mut kernel = Kernel::new();
    let star = kernel.star().expect("star");
    let bool_ty = kernel.bool_ty(star).expect("bool type");
    let mut tower = bool_ty;
    for _ in 0..depth {
        tower = kernel.ty_arr(tower, tower).expect("doubling");
    }
    let arrow = kernel.ty_arr(tower, tower).expect("function type");
    let function = kernel.tm_fv(0, arrow).expect("function variable");
    let binder = kernel.tm_fv(1, tower).expect("binder");
    let body = kernel.app(function, binder).expect("application");
    let source = kernel.lam(binder, body).expect("abstraction");

    let minted = kernel.classifier(source).expect("function type");
    Prover::new(star)
        .union_equal(&mut kernel, minted, arrow)
        .expect("merge the duplicate arrows");
    kernel.tm_eta_fact(None, source)
}

#[test]
fn freshness_stays_decidable_as_terms_share_subterms() {
    // The occurrence walk used to spend one step of fuel per arena row and then
    // give up with a conservative "occurs", so a shared subterm made every
    // freshness-guarded rule stop working at about ten rows. `λv. f v` is an
    // eta redex whatever the type looks like.
    for depth in 0..14 {
        assert!(
            eta_at_depth(depth).is_ok(),
            "`λv. f v` is an eta redex at depth {depth}"
        );
    }
}

#[test]
fn freshness_still_rejects_a_genuine_occurrence_at_depth() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let mut tower = bool_ty;
    for _ in 0..8 {
        tower = fix.ty_arr(tower, tower).expect("doubling");
    }
    let curried = fix.ty_arr(bool_ty, tower).expect("bool -> tower");
    let outer = fix.tm_fv(0, curried).expect("curried function");
    let binder = fix.var(1);
    let function = fix.app(outer, binder).expect("partial application");
    let arrow = fix.ty_arr(bool_ty, tower).expect("bool -> tower");
    let _ = arrow;
    let body = fix.app(function, binder);
    // `function : tower`, whose class contains an arrow only if `tower` is one.
    if let Ok(body) = body {
        let source = fix.lam(binder, body).expect("abstraction");
        assert!(
            fix.tm_eta_fact(None, source).is_err(),
            "the binder still occurs in the function"
        );
    }
}

#[test]
fn a_decoded_arena_consumes_every_byte_it_was_given() {
    // Padding used to be ignored, so one arena had unlimited content addresses.
    let canonical = ArenaCbor::new().bytes();
    assert!(wire::deserialize(canonical.as_slice()).is_ok());

    for suffix in [&[0x00][..], &[0xff, 0xff][..], &canonical[..]] {
        let mut padded = canonical.clone();
        padded.extend_from_slice(suffix);
        assert!(
            wire::deserialize(padded.as_slice()).is_err(),
            "padding must not decode"
        );
        assert!(Table::try_from(CasFact::from_bytes(padded)).is_err());
    }
}

#[test]
fn truncated_bytes_are_still_a_decode_failure() {
    let canonical = ArenaCbor::new().defs(vec![]).bytes();
    for length in 1..canonical.len() {
        assert!(
            wire::deserialize(&canonical[..length]).is_err(),
            "a {length}-byte prefix is not an arena"
        );
    }
}
