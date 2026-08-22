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

use crate::expr::{Expr, Symbol};

/// A variable substitution: variable name → replacement body (a sequence of
/// math symbols, i.e. an expression with its typecode stripped).
///
/// An **association list**, not a map. A substitution has exactly one entry per
/// floating hypothesis of the frame being applied, and mandatory frames are
/// small: 5.04 floats on average across `set.mm`, 40 at the widest. At that
/// size a linear scan of one contiguous allocation beats a `BTreeMap`'s pointer
/// chase into a boxed node, and lookup is the hot operation — `apply_subst`
/// performs one per symbol of every schema it instantiates, and misses on most
/// of them, since a body is mostly constants.
///
/// Entries stay in insertion order, which is the frame's own float order, so
/// iteration is as deterministic for diagnostics as the `BTreeMap` was.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Subst {
    entries: Vec<(Symbol, Vec<Symbol>)>,
}

impl Subst {
    /// An empty substitution.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// An empty substitution with room for `capacity` bindings. The count is
    /// known up front — it is the frame's float count — so the one allocation
    /// this makes can be the only one.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// The body `name` is replaced by, if it is substituted at all.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&[Symbol]> {
        self.entries
            .iter()
            .find(|(var, _)| var.as_str() == name)
            .map(|(_, body)| body.as_slice())
    }

    /// Bind `name` to `body`, returning the binding it replaced.
    pub fn insert(&mut self, name: Symbol, body: Vec<Symbol>) -> Option<Vec<Symbol>> {
        if let Some((_, existing)) = self.entries.iter_mut().find(|(var, _)| *var == name) {
            return Some(std::mem::replace(existing, body));
        }
        self.entries.push((name, body));
        None
    }

    /// The bindings, in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &[Symbol])> {
        self.entries
            .iter()
            .map(|(var, body)| (var, body.as_slice()))
    }

    /// How many variables are substituted.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether nothing is substituted.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

impl FromIterator<(Symbol, Vec<Symbol>)> for Subst {
    fn from_iter<I: IntoIterator<Item = (Symbol, Vec<Symbol>)>>(iter: I) -> Self {
        let mut subst = Self::new();
        for (name, body) in iter {
            subst.insert(name, body);
        }
        subst
    }
}

/// Apply a substitution to a schema expression, splicing each substituted
/// variable's replacement body in place. The typecode is never substituted.
#[must_use]
pub fn apply_subst(schema: &Expr, subst: &Subst) -> Expr {
    let mut body = Vec::with_capacity(schema.body.len());
    for sym in &schema.body {
        if let Some(replacement) = subst.get(sym.as_str()) {
            body.extend_from_slice(replacement);
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
            .map(|(v, e)| (Symbol::from(*v), e.body.clone()))
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
    fn insert_replaces_an_existing_binding() {
        // The scan has to find a repeated name rather than shadow it with a
        // second entry, which `get` would never reach.
        let mut s = Subst::new();
        assert_eq!(s.insert(Symbol::new("ph"), vec![Symbol::new("a")]), None);
        assert_eq!(
            s.insert(Symbol::new("ph"), vec![Symbol::new("b")]),
            Some(vec![Symbol::new("a")])
        );
        assert_eq!(s.len(), 1);
        assert_eq!(s.get("ph"), Some(&[Symbol::new("b")][..]));
    }

    #[test]
    fn iteration_follows_insertion_order() {
        // Diagnostics used to iterate a `BTreeMap`, so order was sorted and
        // therefore reproducible; insertion order has to be reproducible too.
        let s = subst(&[
            ("ps", make_expr("wff", ["b"])),
            ("ph", make_expr("wff", ["a"])),
        ]);
        let names: Vec<&str> = s.iter().map(|(var, _)| var.as_str()).collect();
        assert_eq!(names, ["ps", "ph"]);
    }

    #[test]
    fn vars_collected() {
        let body = make_expr("_", ["(", "x", "+", "y", ")"]).body;
        let is_var = |s: &str| matches!(s, "x" | "y");
        assert_eq!(vars_in_body(&body, &is_var), vec!["x", "y"]);
    }
}
