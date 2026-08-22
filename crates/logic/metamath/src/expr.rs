//! The primitive Metamath expression type.
//!
//! A Metamath expression is a typecode followed by a flat sequence of math
//! symbols. We model it as a **dedicated primitive struct** [`Expr`] — a
//! `typecode` symbol plus an owned `body: Vec<Symbol>` — rather than routing
//! everything through a generic syntax tree. The flat-sequence shape is preserved exactly
//! (no structured grammar tree); see the crate-level docs for why this
//! *faithful-flat-sequence* model is the trusted one.
//!
//! Symbols are owned [`smol_str::SmolStr`]s (cheap to clone, inline for short
//! tokens). Interning for `set.mm` scale is a deferred SKELETON — owned symbols
//! are correct and simple for the hand-encoded theories the crate verifies
//! today.
//!
//! Whether a given symbol is a *variable* (substitutable) or a *constant* is
//! not stored in the expression — it is a property of the surrounding
//! [`crate::Database`]. The expression layer is purely syntactic.

/// A Metamath math symbol (typecode or body token). Owned, cheap-to-clone.
///
/// We use [`smol_str::SmolStr`] for inline small-string storage.
pub type Symbol = smol_str::SmolStr;

/// A Metamath expression: a typecode plus a flat body of math symbols.
///
/// Faithful to Metamath semantics: `( wff ( ph -> ps ) )` is
/// `typecode = "wff"`, `body = ["(", "ph", "->", "ps", ")"]` — *not* a nested
/// tree. Substitution splices symbol sequences in place (see the `subst` module).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    /// The typecode constant (e.g. `wff`, `term`, `class`, `|-`).
    pub typecode: Symbol,
    /// The flat body sequence (everything after the typecode).
    pub body: Vec<Symbol>,
}

impl Expr {
    /// Construct an expression from a typecode and a body sequence.
    pub fn new(typecode: impl Into<Symbol>, body: Vec<Symbol>) -> Self {
        Self {
            typecode: typecode.into(),
            body,
        }
    }

    /// The typecode (head symbol) of the expression.
    pub fn typecode(&self) -> &str {
        self.typecode.as_str()
    }

    /// The body (everything after the typecode) as a symbol slice.
    pub fn body(&self) -> &[Symbol] {
        &self.body
    }

    /// All symbol names (typecode first, then body), in order.
    pub fn symbols(&self) -> impl Iterator<Item = &str> {
        std::iter::once(self.typecode.as_str()).chain(self.body.iter().map(Symbol::as_str))
    }

    /// Render to the flat Metamath surface form (`typecode sym sym ...`).
    pub fn render(&self) -> String {
        let mut out = String::from(self.typecode.as_str());
        for s in &self.body {
            out.push(' ');
            out.push_str(s.as_str());
        }
        out
    }
}

/// Build an expression from a typecode and a sequence of symbol names.
pub fn make_expr<'a>(typecode: &str, body: impl IntoIterator<Item = &'a str>) -> Expr {
    Expr::new(typecode, body.into_iter().map(Symbol::from).collect())
}

/// Build an expression from a flat list of symbol names where the first is the
/// typecode. Returns `None` if `symbols` is empty.
pub fn from_symbols<'a>(symbols: impl IntoIterator<Item = &'a str>) -> Option<Expr> {
    let mut it = symbols.into_iter();
    let typecode = it.next()?;
    Some(Expr::new(typecode, it.map(Symbol::from).collect()))
}

/// The typecode (head symbol) of an expression. Always `Some` for the primitive
/// type; returns `Option` for source-compatibility with the `SExpr` model.
pub fn typecode_of(e: &Expr) -> Option<&str> {
    Some(e.typecode())
}

/// The body (everything after the typecode) of an expression. Always `Some` for
/// the primitive type; kept as `Option` for source-compatibility.
pub fn body_of(e: &Expr) -> Option<&[Symbol]> {
    Some(e.body())
}

/// All symbol names in an expression (typecode included), in order. Always
/// `Some` for the primitive type; kept as `Option` for source-compatibility.
pub fn expr_symbols(e: &Expr) -> Option<Vec<&str>> {
    Some(e.symbols().collect())
}

/// Render an expression back to its flat Metamath surface form
/// (`typecode sym sym ...`), for diagnostics.
pub fn render(e: &Expr) -> String {
    e.render()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let e = make_expr("wff", ["(", "ph", "->", "ps", ")"]);
        assert_eq!(typecode_of(&e), Some("wff"));
        let body: Vec<&str> = body_of(&e).unwrap().iter().map(Symbol::as_str).collect();
        assert_eq!(body, ["(", "ph", "->", "ps", ")"]);
        assert_eq!(render(&e), "wff ( ph -> ps )");
    }

    #[test]
    fn from_symbols_empty_is_none() {
        assert!(from_symbols(std::iter::empty()).is_none());
    }

    #[test]
    fn symbols_all() {
        let e = make_expr("term", ["0"]);
        assert_eq!(expr_symbols(&e), Some(vec!["term", "0"]));
    }
}
