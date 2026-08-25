//! Regression tests for former completeness limits of the syntactic-fact
//! cache.
//!
//! These cases are essential for type-level model selection: substituting a
//! chosen type through a predicate necessarily changes the classifiers of the
//! terms in that predicate.

mod support;

use covalence_logic_hol::SynRel;
use support::Fix;

#[test]
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
