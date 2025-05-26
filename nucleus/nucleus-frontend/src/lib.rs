use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use pretty::RcDoc;
use unicode_ident::{is_xid_continue, is_xid_start};
use winnow::{
    LocatingSlice,
    ascii::{digit1, hex_digit1, multispace1, oct_digit1},
    combinator::{alt, delimited, opt, preceded, repeat, separated},
    prelude::*,
    token::{any, take_till, take_while},
};

/// Top-level syntax
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Term {
    /// An identifier
    Ident(Ident),
    /// A projection
    Proj(Proj),
    /// A natural number
    Nat(String),
    /// A hole
    Hole,
    /// An application
    App(Vec<ArcSyntax>),
    /// A tuple
    Tuple(Vec<ArcSyntax>),
    /// A lambda abstraction
    Lam(Abs),
    /// A forall
    Pi(Abs),
    /// A sigma type
    Sigma(Abs),
    /// A let-binding
    Let(Let),
    /// An equation
    Eqn(Eqn),
    /// An annotation
    Annot(Annot),
    /// The epsilon operator
    Epsilon,
    /// The propositional truncation operator
    Trunc,
}

impl Term {
    /// Check two expressions are equivalent modulo span
    pub fn eqv(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Proj(a), Term::Proj(b)) => a.eqv(b),
            (Term::App(a), Term::App(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.eqv(y))
            }
            (Term::Tuple(a), Term::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.eqv(y))
            }
            (Term::Lam(a), Term::Lam(b)) => a.eqv(b),
            (Term::Pi(a), Term::Pi(b)) => a.eqv(b),
            (Term::Sigma(a), Term::Sigma(b)) => a.eqv(b),
            (Term::Let(a), Term::Let(b)) => a.eqv(b),
            (Term::Eqn(a), Term::Eqn(b)) => a.eqv(b),
            (Term::Annot(a), Term::Annot(b)) => a.eqv(b),
            (l, r) => l == r,
        }
    }

    /// Parse a top-level expression
    ///
    /// # Examples
    /// ```rust
    /// # use winnow::{LocatingSlice, Parser};
    /// # use nucleus_frontend::*;
    /// let valid = [
    ///     "(f g) h", "f (g h) (x y z) = c (w = a) : A = B (∀x : A, B)", "∀x,x",
    ///     "(,)", "(x,)", "(x, y)", "(∀x : A, B, C)", "List.cons", "Nat.add 5 3",
    ///     "let x := 5; 3 = 7", "7 = let x := 5; 3", "#ch (List Nat)",
    /// ];
    /// for expr in valid {
    ///     let parsed = Term::expr_e.parse(LocatingSlice::new(expr)).unwrap();
    ///     for width in [1, 10, 80, 100] {
    ///         let pretty = format!("{}", parsed.to_doc(usize::MAX).pretty(width));
    ///         let reparsed = Term::expr_e.parse(LocatingSlice::new(&pretty)).unwrap();
    ///         assert!(
    ///             parsed.eqv(&reparsed),
    ///             "{} ==> {:?} ≈ {} ==> {:?}", expr, parsed, pretty, reparsed
    ///         );
    ///     }
    /// }
    /// ```
    pub fn expr_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        (
            Term::eq_e.with_span(),
            opt(preceded((opt(ws), ":", opt(ws)), Term::eq_s)),
        )
            .map(|((lhs, span), rhs)| {
                if let Some(rhs) = rhs {
                    Term::Annot(Annot {
                        expr: ArcSyntax::new(lhs, span),
                        annot: rhs,
                    })
                } else {
                    lhs
                }
            })
            .parse_next(input)
    }

    /// Parse a top-level expression with span
    pub fn expr_s(input: &mut LocatingSlice<&str>) -> winnow::Result<ArcSyntax> {
        Term::expr_e
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an equality expression
    pub fn eq_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        (
            Term::app_e.with_span(),
            opt(preceded((opt(ws), "=", opt(ws)), Term::app_s)),
        )
            .map(|((lhs, span), rhs)| {
                if let Some(rhs) = rhs {
                    Term::Eqn(Eqn {
                        lhs: ArcSyntax::new(lhs, span),
                        rhs,
                    })
                } else {
                    lhs
                }
            })
            .parse_next(input)
    }

    /// Parse an equality expression with span
    pub fn eq_s(input: &mut LocatingSlice<&str>) -> winnow::Result<ArcSyntax> {
        Term::eq_e
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an application
    pub fn app_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        alt((
            Let::let_.map(Term::Let),
            (
                Term::abs_e.with_span(),
                repeat(0.., preceded(ws, Term::atom_s)),
            )
                .map(|((lhs, span), mut rhs): (_, Vec<ArcSyntax>)| {
                    if rhs.is_empty() {
                        lhs
                    } else {
                        rhs.insert(0, ArcSyntax::new(lhs, span));
                        Term::App(rhs)
                    }
                }),
        ))
        .parse_next(input)
    }

    /// Parse an application with span
    pub fn app_s(input: &mut LocatingSlice<&str>) -> winnow::Result<ArcSyntax> {
        Term::app_e
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an abstraction expression
    pub fn abs_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        alt((
            preceded((alt(("λ", "\\")), opt(ws)), Abs::dot).map(Term::Lam),
            preceded((alt(("∀", "#pi")), opt(ws)), Abs::dot).map(Term::Pi),
            preceded((alt(("Σ", "#sg")), opt(ws)), Abs::dot).map(Term::Sigma),
            Term::atom_e,
        ))
        .parse_next(input)
    }

    /// Parse an abstraction expression with span
    pub fn abs_s(input: &mut LocatingSlice<&str>) -> winnow::Result<ArcSyntax> {
        Term::abs_e
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse an atomic expression
    pub fn atom_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        (
            alt((
                Term::tuple_e,
                alt((
                    ("0x", hex_digit1).take(),
                    ("0o", oct_digit1).take(),
                    ("0b", take_while(1.., ['0', '1'])).take(),
                    digit1,
                ))
                .map(|x: &str| Term::Nat(x.to_string())),
                Ident::opt_ident.map(|x| x.map(Term::Ident).unwrap_or(Term::Hole)),
                "#ch".map(|_| Term::Epsilon),
                alt(("∃", "#tr")).map(|_| Term::Trunc),
            ))
            .with_span(),
            repeat(
                0..,
                preceded(
                    opt(ws),
                    Field::field
                        .with_span()
                        .map(|(field, span)| Spanned::new(field, span)),
                ),
            ),
        )
            .map(|((base, span), path): (_, Vec<Spanned<Field>>)| {
                if path.is_empty() {
                    base
                } else {
                    Term::Proj(Proj {
                        base: ArcSyntax::new(base, span),
                        path,
                    })
                }
            })
            .parse_next(input)
    }

    /// Parse an atomic expression with span
    pub fn atom_s(input: &mut LocatingSlice<&str>) -> winnow::Result<ArcSyntax> {
        Term::atom_e
            .with_span()
            .map(|(val, span)| Spanned::new(val, span))
            .parse_next(input)
    }

    /// Parse a tuple expression
    pub fn tuple_e(input: &mut LocatingSlice<&str>) -> winnow::Result<Term> {
        delimited(
            ("(", opt(ws)),
            (
                separated(0.., Term::expr_s, (opt(ws), ",", opt(ws))),
                opt((opt(ws), ",")),
            ),
            (opt(ws), ")"),
        )
        .map(|(exprs, trailing): (Vec<ArcSyntax>, _)| {
            if exprs.len() <= 1 && trailing.is_none() {
                if exprs.is_empty() {
                    Term::App(vec![])
                } else {
                    match &*exprs[0].val {
                        Term::App(exprs) => Term::App(exprs.clone()),
                        _ => Term::App(exprs),
                    }
                }
            } else {
                Term::Tuple(exprs)
            }
        })
        .parse_next(input)
    }

    /// Pretty-print an expression with the given precedence level
    pub fn to_doc(&self, precedence: usize) -> RcDoc<()> {
        let result = match self {
            Term::Ident(ident) => ident.to_doc(),
            Term::Proj(proj) => proj.to_doc(),
            Term::Nat(x) => RcDoc::as_string(x),
            Term::Hole => RcDoc::text("_"),
            Term::App(exprs) => {
                if exprs.len() == 0 {
                    return RcDoc::text("()");
                }
                RcDoc::intersperse(
                    exprs.iter().enumerate().map(|(i, e)| {
                        e.to_doc(if i < exprs.len() - 1 {
                            Term::ABS_LEVEL - 1
                        } else {
                            Term::ABS_LEVEL
                        })
                    }),
                    RcDoc::line(),
                )
                .nest(1)
                .group()
            }
            Term::Tuple(exprs) => RcDoc::text("(")
                .append(
                    RcDoc::intersperse(
                        exprs.iter().map(|e| e.to_doc(Term::EQN_LEVEL)),
                        RcDoc::text(",").append(RcDoc::line()),
                    )
                    .nest(1)
                    .group(),
                )
                .append(RcDoc::text(if exprs.len() <= 1 { ",)" } else { ")" })),
            Term::Eqn(eqn) => eqn.to_doc(),
            Term::Lam(abs) => RcDoc::text("λ").append(RcDoc::space()).append(abs.to_doc()),
            Term::Pi(abs) => RcDoc::text("∀").append(RcDoc::space()).append(abs.to_doc()),
            Term::Sigma(abs) => RcDoc::text("Σ").append(RcDoc::space()).append(abs.to_doc()),
            Term::Let(let_) => let_.to_doc(),
            Term::Annot(annot) => annot.to_doc(),
            Term::Epsilon => RcDoc::text("#ch"),
            Term::Trunc => RcDoc::text("∃"),
        };
        if self.precedence() > precedence {
            RcDoc::text("(")
                .append(result)
                .append(RcDoc::text(")"))
                .group()
        } else {
            result
        }
    }

    /// Get this expression's precedence level
    pub fn precedence(&self) -> usize {
        match self {
            Term::Ident(_)
            | Term::Nat(_)
            | Term::Hole
            | Term::Tuple(_)
            | Term::Proj(_)
            | Term::Epsilon
            | Term::Trunc => Term::ATOM_LEVEL,
            Term::App(_) | Term::Let(_) => Term::APP_LEVEL,
            Term::Lam(_) | Term::Pi(_) | Term::Sigma(_) => Term::ABS_LEVEL,
            Term::Eqn(_) => Term::EQN_LEVEL,
            Term::Annot(_) => Term::ANNOT_LEVEL,
        }
    }

    /// The precedence level for an atom
    pub const ATOM_LEVEL: usize = 0;

    /// The precedence level for an abstraction
    pub const ABS_LEVEL: usize = 1;

    /// The precedence level for an application
    pub const APP_LEVEL: usize = 2;

    /// The precedence level for an equation
    pub const EQN_LEVEL: usize = 3;

    /// The precedence level for an annotation
    pub const ANNOT_LEVEL: usize = 4;
}

/// An expression with span, wrapped in an [`Arc`]
pub type ArcSyntax = Spanned<Arc<Term>>;

/// An identifier
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Ident(pub String);

/// A projection
#[derive(Debug, Clone, Eq, PartialEq, Hash)]

pub struct Proj {
    /// The base expression
    pub base: ArcSyntax,
    /// The path
    pub path: Vec<Spanned<Field>>,
}

impl Proj {
    /// Check whether two projections are equivalent modulo span
    pub fn eqv(&self, other: &Proj) -> bool {
        self.base.eqv(&other.base) && self.path == other.path
    }

    /// Pretty-print a projection
    pub fn to_doc(&self) -> RcDoc<()> {
        let mut result = self.base.to_doc(Term::ATOM_LEVEL);
        for field in &self.path {
            result = result.append(RcDoc::text(".")).append(field.to_doc());
        }
        result
    }
}

/// A field in a projection
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Field(pub String);

/// An abstraction
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Abs {
    /// The parameter
    pub param: ArcSyntax,
    /// The body
    pub body: ArcSyntax,
}

impl Abs {
    /// Check whether two abstractions are equivalent modulo span
    pub fn eqv(&self, other: &Abs) -> bool {
        self.param.eqv(&other.param) && self.body.eqv(&other.body)
    }

    /// Parse an abtraction separated by a dot
    pub fn dot(input: &mut LocatingSlice<&str>) -> winnow::Result<Abs> {
        (Term::expr_s, (opt(ws), ",", opt(ws)), Term::expr_s)
            .map(|(param, _, body)| Abs { param, body })
            .parse_next(input)
    }

    /// Pretty-print an abstraction separated by a dot
    pub fn to_doc(&self) -> RcDoc<()> {
        self.param
            .to_doc(Term::ANNOT_LEVEL)
            .append(RcDoc::space())
            .append(RcDoc::text(","))
            .append(RcDoc::line())
            .append(self.body.to_doc(Term::ANNOT_LEVEL))
            .group()
    }
}

/// An equation
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Eqn {
    /// The left-hand side
    pub lhs: ArcSyntax,
    /// The right-hand side
    pub rhs: ArcSyntax,
}

impl Eqn {
    /// Check whether two equations are equivalent modulo span
    pub fn eqv(&self, other: &Eqn) -> bool {
        self.lhs.eqv(&other.lhs) && self.rhs.eqv(&other.rhs)
    }

    /// Pretty-print an equation
    pub fn to_doc(&self) -> RcDoc<()> {
        self.lhs
            .to_doc(Term::EQN_LEVEL - 1)
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::line())
            .append(self.rhs.to_doc(Term::EQN_LEVEL - 1))
            .group()
    }
}

/// A let-binding
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Let {
    /// The pattern being bound
    pub pattern: ArcSyntax,
    /// The bound expression
    pub bound: ArcSyntax,
    /// The body of the let-binding
    pub body: ArcSyntax,
}

impl Let {
    /// Check whether two let-bindings are equivalent modulo span
    pub fn eqv(&self, other: &Let) -> bool {
        self.pattern.eqv(&other.pattern)
            && self.bound.eqv(&other.bound)
            && self.body.eqv(&other.body)
    }

    /// Parse a let-binding
    pub fn let_(input: &mut LocatingSlice<&str>) -> winnow::Result<Let> {
        (
            preceded("let", ws),
            Term::expr_s,
            preceded((opt(ws), ":=", opt(ws)), Term::expr_s),
            preceded((opt(ws), ";", opt(ws)), Term::expr_s),
        )
            .map(|(_, pattern, bound, body)| Let {
                pattern,
                bound,
                body,
            })
            .parse_next(input)
    }

    /// Pretty-print a let-binding
    pub fn to_doc(&self) -> RcDoc<()> {
        RcDoc::text("let")
            .append(RcDoc::space())
            .append(self.pattern.to_doc(Term::ANNOT_LEVEL))
            .append(RcDoc::space())
            .append(RcDoc::text(":="))
            .append(RcDoc::line())
            .append(self.bound.to_doc(Term::ANNOT_LEVEL))
            .append(RcDoc::space())
            .append(RcDoc::text(";"))
            .append(RcDoc::line())
            .append(self.body.to_doc(Term::ANNOT_LEVEL))
            .group()
    }
}

/// An annotation
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Annot {
    /// The expression being annotated
    pub expr: ArcSyntax,
    /// The annotation
    pub annot: ArcSyntax,
}

impl Annot {
    /// Check whether two annotations are equivalent modulo span
    pub fn eqv(&self, other: &Annot) -> bool {
        self.expr.eqv(&other.expr) && self.annot.eqv(&other.annot)
    }

    /// Pretty-print an annotation
    pub fn to_doc(&self) -> RcDoc<()> {
        self.expr
            .to_doc(Term::ANNOT_LEVEL - 1)
            .append(RcDoc::space())
            .append(RcDoc::text(":"))
            .append(RcDoc::line())
            .append(self.annot.to_doc(Term::ANNOT_LEVEL - 1))
            .group()
    }
}

impl From<String> for Ident {
    fn from(value: String) -> Self {
        Ident(value)
    }
}

impl From<&'_ str> for Ident {
    fn from(value: &'_ str) -> Self {
        Ident(value.to_string())
    }
}

impl Ident {
    /// Keywords
    pub const KEYWORDS: &'static [&'static str] = &["λ", "∀", "Σ", "let", "def", "pub"];

    /// Parse an identifier
    ///
    /// See [`Ident::opt_ident`] for details.
    pub fn ident(input: &mut LocatingSlice<&str>) -> winnow::Result<Ident> {
        Ident::take.map(|x| Ident(x.to_string())).parse_next(input)
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
    /// # use nucleus_frontend::*;
    /// assert_eq!(Ident::opt_ident.parse(LocatingSlice::new("_")).unwrap(), None);
    /// let valid = [
    ///     "x", "xy", "x3", "x123", "my_obj", "__obj", "你好", "جاد", "x'", "x₁",
    /// ];
    /// for ident in valid {
    ///     assert_eq!(
    ///         Ident::opt_ident.parse(LocatingSlice::new(ident)).unwrap(),
    ///         Some(ident.into())
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
            .map(|x| x.map(|x| Ident(x.to_string())))
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
            .verify(|x| !Ident::KEYWORDS.contains(&x))
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
        (is_xid_start(x) || x == '_') && x != 'λ' && x != 'Σ'
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

impl Field {
    /// Parse a field
    pub fn field(input: &mut LocatingSlice<&str>) -> winnow::Result<Field> {
        preceded(".", take_while(1.., Ident::ident_continue))
            .map(|x: &str| Field(x.to_string()))
            .parse_next(input)
    }

    /// Pretty print a field
    pub fn to_doc(&self) -> RcDoc<()> {
        // TODO: escape invalid fields
        RcDoc::as_string(&self.0)
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
