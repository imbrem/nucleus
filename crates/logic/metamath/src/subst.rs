//! The substitution engine — the heart of "Metamath-style rewrite".
//!
//! A Metamath substitution maps each variable to a sequence of math symbols
//! (the *body* of an expression of the variable's typecode). Applying a
//! substitution to a schema walks its body symbol sequence and, for every
//! symbol that is a substituted variable, **splices** the replacement body in
//! place. Constants and unmapped symbols pass through unchanged.
//!
//! On the primitive flat [`Expr`] the typecode is always a constant (never a
//! variable), so it is copied verbatim, and the body symbols are spliced.

use std::collections::BTreeMap;

use crate::expr::{Expr, Symbol};

/// A variable substitution: variable name → replacement body (a sequence of
/// math symbols, i.e. an expression with its typecode stripped).
///
/// We use a `BTreeMap` for deterministic iteration in diagnostics.
pub type Subst = BTreeMap<String, Vec<Symbol>>;

/// Apply a substitution to a schema expression, splicing each substituted
/// variable's replacement body in place. The typecode is never substituted.
pub fn apply_subst(schema: &Expr, subst: &Subst) -> Expr {
    let mut body = Vec::with_capacity(schema.body.len());
    for sym in &schema.body {
        if let Some(replacement) = subst.get(sym.as_str()) {
            body.extend(replacement.iter().cloned());
        } else {
            body.push(sym.clone());
        }
    }
    Expr::new(schema.typecode.clone(), body)
}

/// Collect the distinct variable names appearing in a substituted body, given
/// the set of names that are variables. Used for $d checking: a $d on
/// `(a, b)` requires that the variables occurring in `subst(a)` and `subst(b)`
/// are disjoint.
pub fn vars_in_body<'a>(body: &'a [Symbol], is_variable: &impl Fn(&str) -> bool) -> Vec<&'a str> {
    // O(n) dedup (a `Vec::contains` scan here was quadratic per body, and this
    // runs for every $d pair of every assertion application on the set.mm path).
    let mut seen = Vec::new();
    let mut seen_set: fnv::FnvHashSet<&str> = fnv::FnvHashSet::default();
    for sym in body {
        let n = sym.as_str();
        if is_variable(n) && seen_set.insert(n) {
            seen.push(n);
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{make_expr, render};

    fn subst(pairs: &[(&str, Expr)]) -> Subst {
        pairs
            .iter()
            .map(|(v, e)| (v.to_string(), e.body.clone()))
            .collect()
    }

    #[test]
    fn splice_single_variable() {
        // schema: wff ( ph -> ps ) ; ph := ( ph -> ps ), ps := ch
        let schema = make_expr("wff", ["(", "ph", "->", "ps", ")"]);
        let s = subst(&[
            ("ph", make_expr("wff", ["(", "ph", "->", "ps", ")"])),
            ("ps", make_expr("wff", ["ch"])),
        ]);
        let r = apply_subst(&schema, &s);
        assert_eq!(render(&r), "wff ( ( ph -> ps ) -> ch )");
    }

    #[test]
    fn typecode_preserved() {
        // The head typecode is a constant and is never substituted.
        let schema = make_expr("term", ["t"]);
        let s = subst(&[("t", make_expr("term", ["(", "x", "+", "y", ")"]))]);
        let r = apply_subst(&schema, &s);
        assert_eq!(render(&r), "term ( x + y )");
    }

    #[test]
    fn unmapped_symbols_passthrough() {
        let schema = make_expr("wff", ["0", "=", "0"]);
        let s = subst(&[]);
        assert_eq!(render(&apply_subst(&schema, &s)), "wff 0 = 0");
    }

    #[test]
    fn vars_collected() {
        let body = make_expr("_", ["(", "x", "+", "y", ")"]).body;
        let is_var = |s: &str| matches!(s, "x" | "y");
        assert_eq!(vars_in_body(&body, &is_var), vec!["x", "y"]);
    }
}
