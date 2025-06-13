/*!
S-expression parsing
*/

use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use pretty::RcDoc;
use smol_str::SmolStr;
use unicode_ident::{is_xid_continue, is_xid_start};
use winnow::{
    LocatingSlice,
    ascii::{alphanumeric1, digit1, hex_digit1, multispace1, oct_digit1},
    combinator::{alt, delimited, opt, preceded, separated},
    prelude::*,
    token::{any, take_till, take_while},
};

/// An S-expression
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Sexpr {
    /// An identifier
    Ident(Ident),
    /// A numeral
    Numeral(Numeral),
    /// A field
    Field(Field),
    /// A keyword
    Kw(Kw),
    /// A list
    List(Vec<LSexpr>),
}

impl Sexpr {
    /// Compare S-expressions up to span
    pub fn eqv(&self, other: &Sexpr) -> bool {
        if self as *const _ == other as *const _ {
            return true; // fast path for identical references
        }
        match (self, other) {
            (Sexpr::List(a), Sexpr::List(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.eqv(y))
            }
            (a, b) => a == b,
        }
    }

    /// Parse a sequence of S-expressions
    pub fn lsexprs(input: &mut LocatingSlice<&str>) -> winnow::Result<Vec<LSexpr>> {
        separated(0.., Sexpr::lsexpr, ws).parse_next(input)
    }

    /// Parse an S-expression with span
    pub fn lsexpr(input: &mut LocatingSlice<&str>) -> winnow::Result<LSexpr> {
        Sexpr::sexpr
            .with_span()
            .map(|(val, span)| Arc::new(Spanned::new(val, span)))
            .parse_next(input)
    }

    /// Parse an S-expression
    pub fn sexpr(input: &mut LocatingSlice<&str>) -> winnow::Result<Sexpr> {
        alt((
            Ident::ident.map(Sexpr::Ident),
            Numeral::numeral.map(Sexpr::Numeral),
            Field::field.map(Sexpr::Field),
            Kw::kw.map(Sexpr::Kw),
            delimited(
                ("(", opt(ws)),
                Sexpr::lsexprs.map(Sexpr::List),
                (opt(ws), ")"),
            ),
        ))
        .parse_next(input)
    }

    /// Whether this S-expression is an atom
    pub fn is_atom(&self) -> bool {
        !matches!(self, Sexpr::List(_))
    }

    /// Pretty print an S-expression
    pub fn to_doc(&self) -> RcDoc<()> {
        match self {
            Sexpr::Ident(ident) => ident.to_doc(),
            Sexpr::Numeral(numeral) => numeral.to_doc(),
            Sexpr::Field(field) => field.to_doc(),
            Sexpr::Kw(kw) => kw.to_doc(),
            Sexpr::List(list) => RcDoc::text("(")
                .append(
                    RcDoc::intersperse(list.iter().map(|x| x.to_doc()), RcDoc::line())
                        .nest(1)
                        .group(),
                )
                .append(RcDoc::text(")")),
        }
    }
}

impl From<Ident> for Sexpr {
    fn from(ident: Ident) -> Self {
        Sexpr::Ident(ident)
    }
}

impl From<Numeral> for Sexpr {
    fn from(numeral: Numeral) -> Self {
        Sexpr::Numeral(numeral)
    }
}

impl From<Field> for Sexpr {
    fn from(field: Field) -> Self {
        Sexpr::Field(field)
    }
}

impl From<Kw> for Sexpr {
    fn from(kw: Kw) -> Self {
        Sexpr::Kw(kw)
    }
}

impl From<Vec<LSexpr>> for Sexpr {
    fn from(list: Vec<LSexpr>) -> Self {
        Sexpr::List(list)
    }
}

/// An S-expression with a span
pub type LSexpr = Arc<Spanned<Sexpr>>;

/// An identifier
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Ident(SmolStr);

impl Deref for Ident {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A numeral
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Numeral(SmolStr);

impl Deref for Numeral {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A field
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Field(SmolStr);

impl Deref for Field {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A keyword
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Kw(SmolStr);

impl Deref for Kw {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Ident {
    /// Create a new identifier from a static string
    pub const fn new_static(text: &'static str) -> Self {
        Ident(SmolStr::new_static(text))
    }

    /// Parse an identifier
    ///
    /// See [`Ident::opt_ident`] for details.
    pub fn ident(input: &mut LocatingSlice<&str>) -> winnow::Result<Ident> {
        Ident::take.map(|x| Ident(x.into())).parse_next(input)
    }

    /// Parse an identifier with a span
    ///
    /// See [`Ident::opt_ident`] for details.
    pub fn ident_s(input: &mut LocatingSlice<&str>) -> winnow::Result<Spanned<Ident>> {
        Ident::ident
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an identifier
    ///
    /// Returns `None` if the result is a hole
    ///
    /// # Examples
    /// ```
    /// # use winnow::{LocatingSlice, Parser};
    /// # use nucleus_frontend::sexpr::*;
    /// assert_eq!(Ident::opt_ident.parse(LocatingSlice::new("_")).unwrap(), None);
    /// let valid = [
    ///     "x", "xy", "x3", "x123", "my_obj", "__obj", "你好", "جاد", "x'", "x₁",
    /// ];
    /// for ident in valid {
    ///     assert_eq!(
    ///         Ident::opt_ident.parse(LocatingSlice::new(ident)).unwrap().as_deref(),
    ///         Some(ident)
    ///     );
    /// }
    /// let invalid = [
    ///     "x+y", "x + y", "λ", "()", "(x)", "x[5]", "$x", "x+", "₀x",
    ///     "∀", "∀x", "x∀", "∃", "∃x", "x∃"
    /// ];
    /// for ident in invalid {
    ///     assert!(Ident::opt_ident.parse(LocatingSlice::new(ident)).is_err());
    /// }
    /// ```
    pub fn opt_ident(input: &mut LocatingSlice<&str>) -> winnow::Result<Option<Ident>> {
        Ident::take_opt
            .map(|x| x.map(|x| Ident(x.into())))
            .parse_next(input)
    }

    /// Parse an identifier with a span
    ///
    /// See [`Ident::opt_ident`] for details.
    pub fn opt_ident_s(input: &mut LocatingSlice<&str>) -> winnow::Result<Spanned<Option<Ident>>> {
        Ident::opt_ident
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an identifier
    ///
    /// See [`Ident::opt_ident`] for details.
    pub fn take<'s>(input: &mut LocatingSlice<&'s str>) -> winnow::Result<&'s str> {
        Ident::take_opt.verify_map(|x| x).parse_next(input)
    }

    /// Parse an identifier
    ///
    /// See [`Ident::opt_ident`] for details.
    ///
    /// Returns `None` if the result is a hole
    pub fn take_opt<'s>(input: &mut LocatingSlice<&'s str>) -> winnow::Result<Option<&'s str>> {
        (
            any.verify(|x| Ident::ident_start(*x)),
            take_till(.., |x| !Ident::ident_continue(x)),
        )
            .take()
            .map(|x| if x == "_" { None } else { Some(x) })
            .parse_next(input)
    }

    /// Pretty print an identifier
    pub fn to_doc(&self) -> RcDoc<()> {
        //TODO: escape invalid identifiers
        RcDoc::as_string(&self.0)
    }

    /// Whether a character can appear at the start of an identifier
    pub fn ident_start(x: char) -> bool {
        (is_xid_start(x) || x == '_') && x != 'λ' && x != 'Σ' && x != 'Π'
    }

    /// Whether a character can continue an identifier
    pub fn ident_continue(x: char) -> bool {
        (is_xid_continue(x)
            || x == '\''
            || x == '₀'
            || x == '₁'
            || x == '₂'
            || x == '₃'
            || x == '₄'
            || x == '₅'
            || x == '₆'
            || x == '₇'
            || x == '₈'
            || x == '₉')
            && x != 'λ'
            && x != 'Σ'
            && x != 'Π'
    }
}

impl Numeral {
    /// Create a new numeral from a static string
    pub const fn new_static(text: &'static str) -> Self {
        Numeral(SmolStr::new_static(text))
    }

    /// Parse a numeral
    pub fn numeral(input: &mut LocatingSlice<&str>) -> winnow::Result<Numeral> {
        alt((
            digit1,
            preceded("0x", hex_digit1),
            preceded("0o", oct_digit1),
            preceded("0b", take_while(1.., [b'0', b'1'])),
        ))
        .map(|x: &str| Numeral(x.into()))
        .parse_next(input)
    }

    /// Pretty print a numeral
    pub fn to_doc(&self) -> RcDoc<()> {
        RcDoc::as_string(&self.0)
    }
}

impl Field {
    /// Create a new field from a static string
    pub const fn new_static(text: &'static str) -> Self {
        Field(SmolStr::new_static(text))
    }

    /// Parse a field
    pub fn field(input: &mut LocatingSlice<&str>) -> winnow::Result<Field> {
        preceded(".", take_while(1.., Ident::ident_continue))
            .map(|x: &str| Field(x.into()))
            .parse_next(input)
    }

    /// Pretty print a field
    pub fn to_doc(&self) -> RcDoc<()> {
        RcDoc::text(".").append(RcDoc::as_string(&self.0))
    }
}

impl Kw {
    /// The keyword for imports
    pub const IMPORT: Self = Self::new_static("import");

    /// The keyword for exports
    pub const EXPORT: Self = Self::new_static("export");

    /// The keyword for local declarations
    pub const LOCAL: Self = Self::new_static("local");

    /// The keyword for definitions
    pub const DEF: Self = Self::new_static("def");

    /// The keyword for universe levels
    pub const TY: Self = Self::new_static("ty");

    /// The keyword for dependent function types
    pub const PI: Self = Self::new_static("pi");

    /// The keyword for abstractions
    pub const FN: Self = Self::new_static("fn");

    /// The keyword let
    pub const LET: Self = Self::new_static("let");

    /// The keyword for the identity type
    pub const IS: Self = Self::new_static("is");

    /// The keyword for an annotation
    pub const ANNOT: Self = Self::new_static("annot");

    /// The keyword for true
    pub const TT: Self = Self::new_static("tt");

    /// The keyword for false
    pub const FF: Self = Self::new_static("ff");

    /// The keyword for a dependent if-then-else
    pub const IF: Self = Self::new_static("if");

    /// The keyword for a propositional truncation
    pub const TRUNC: Self = Self::new_static("ih");

    /// The keyword for Hilbert's ε
    pub const EPSILON: Self = Self::new_static("ch");

    /// The keyword for the natural numbers
    pub const NAT: Self = Self::new_static("N");

    /// The keyword for the integers
    pub const INT: Self = Self::new_static("Z");

    /// The keyword for a structure type
    pub const STRUCT: Self = Self::new_static("st");

    /// The keyword for a structure type's constructor
    pub const MK: Self = Self::new_static("mk");

    /// The keyword for a projection from a structure type
    pub const PROJ: Self = Self::new_static("pr");

    /// The keyword for the null context
    pub const NIL: Self = Self::new_static("nil");

    /// The keyword for context append
    pub const CONS: Self = Self::new_static("cons");

    /// Create a new keyword from a static string
    pub const fn new_static(text: &'static str) -> Self {
        Kw(SmolStr::new_static(text))
    }

    /// Parse a keyword
    pub fn kw(input: &mut LocatingSlice<&str>) -> winnow::Result<Kw> {
        preceded("#", alphanumeric1)
            .map(|x: &str| Kw(x.into()))
            .parse_next(input)
    }

    /// Pretty print a keyword
    pub fn to_doc(&self) -> RcDoc<()> {
        RcDoc::text("#").append(RcDoc::as_string(&self.0))
    }
}

/// A value annotated with its source span
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Spanned<T> {
    pub val: T,
    pub span: std::ops::Range<usize>,
}

impl<T> Spanned<T> {
    /// Construct a new spanned value
    pub fn new(val: impl Into<T>, span: std::ops::Range<usize>) -> Self {
        Spanned {
            val: val.into(),
            span,
        }
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.val
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.val
    }
}

/// Parse whitespace
pub fn ws<'s>(input: &mut LocatingSlice<&'s str>) -> winnow::Result<&'s str> {
    multispace1.parse_next(input)
}
