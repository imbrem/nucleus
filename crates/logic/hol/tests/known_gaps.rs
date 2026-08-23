//! Completeness gaps found while reviewing the syntactic-fact cache.
//!
//! Nothing here is a soundness problem: every case is the kernel refusing a
//! derivation it should accept. Each gap gets two tests, one that passes and
//! pins down what the kernel does today, and one marked `#[ignore]` that states
//! what it should do. Run the second set with
//! `cargo test -p covalence-logic-hol -- --ignored`; each must start passing
//! when its gap closes, and its companion must be updated in the same change.

mod support;

use covalence_logic_hol::{KernelError, SynRel};
use support::Fix;

#[test]
fn today_a_type_substitution_cannot_be_pushed_into_a_term() {
    // Every congruence checks that its two endpoints carry union-find-equal
    // classifiers. That is right for a direct fact, but a substitution fact
    // relates endpoints whose classifiers the substitution itself rewrites, so
    // `[bool / α] (x : α) = (x : bool)` is rejected out of hand and a type
    // variable can never be instantiated inside a term.
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let alpha = fix.ty_fv(7, star).expect("type variable");
    let at_alpha = fix.tm_fv(0, alpha).expect("x : α");
    let at_bool = fix.tm_fv(0, bool_ty).expect("x : bool");

    let annotation = fix
        .syn_sub_var(None, alpha, bool_ty)
        .expect("`[bool / α] α = bool` is fine on its own");
    assert!(matches!(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(alpha),
            Some(bool_ty),
            at_alpha,
            at_bool,
            &[annotation],
        ),
        Err(KernelError::ClassifierMismatch { .. })
    ));
}

#[test]
#[ignore = "gap: endpoint compatibility should not be required of a substitution fact"]
fn a_type_substitution_must_reach_the_terms_it_retypes() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let alpha = fix.ty_fv(7, star).expect("type variable");
    let at_alpha = fix.tm_fv(0, alpha).expect("x : α");
    let at_bool = fix.tm_fv(0, bool_ty).expect("x : bool");

    let annotation = fix.syn_sub_var(None, alpha, bool_ty).expect("sub var");
    assert!(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(alpha),
            Some(bool_ty),
            at_alpha,
            at_bool,
            &[annotation],
        )
        .is_ok(),
        "instantiating a type variable is the point of having one"
    );
}

#[test]
fn today_an_annotation_that_moves_blocks_its_own_substitution() {
    // The same restriction from the other side. `[true / x] (y : model 9 x)`
    // has a provable annotation obligation, `[true / x] (model 9 x) = model 9
    // true`, but the congruence built from it is refused because `model 9 x`
    // and `model 9 true` are not union-find equal — and they cannot be, since
    // they are genuinely different types.
    let mut fix = Fix::new();
    let subject = fix.var(0);
    let value = fix.lit(true);
    let guard = fix.model(9, subject).expect("model 9 x");
    let annotated = fix.tm_fv(1, guard).expect("y : model 9 x");
    let rewritten_guard = fix.model(9, value).expect("model 9 true");
    let rewritten = fix.tm_fv(1, rewritten_guard).expect("y : model 9 true");
    let witness = fix.ty_var(9);

    let inner = fix.syn_sub_var(None, subject, value).expect("sub var");
    let annotation = fix
        .syn_implicit_binder_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            guard,
            rewritten_guard,
            witness,
            inner,
        )
        .expect("the annotation obligation is provable");
    assert!(matches!(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            annotated,
            rewritten,
            &[annotation],
        ),
        Err(KernelError::ClassifierMismatch { .. })
    ));
}

#[test]
#[ignore = "gap: a substitution fact should relate endpoints whose classifiers it rewrites"]
fn a_substituted_annotation_must_reach_the_variable_that_carries_it() {
    let mut fix = Fix::new();
    let subject = fix.var(0);
    let value = fix.lit(true);
    let guard = fix.model(9, subject).expect("model 9 x");
    let annotated = fix.tm_fv(1, guard).expect("y : model 9 x");
    let rewritten_guard = fix.model(9, value).expect("model 9 true");
    let rewritten = fix.tm_fv(1, rewritten_guard).expect("y : model 9 true");
    let witness = fix.ty_var(9);

    let inner = fix.syn_sub_var(None, subject, value).expect("sub var");
    let annotation = fix
        .syn_implicit_binder_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            guard,
            rewritten_guard,
            witness,
            inner,
        )
        .expect("the annotation obligation is provable");
    assert!(
        fix.syn_congr(
            None,
            SynRel::Syn,
            Some(subject),
            Some(value),
            annotated,
            rewritten,
            &[annotation],
        )
        .is_ok(),
        "`[true / x] (y : model 9 x)` is `y : model 9 true`"
    );
}
