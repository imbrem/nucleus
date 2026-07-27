//! Streaming construction and emission of untagged S-expressions.
//!
//! The interfaces here deliberately separate syntax from data models. A
//! dialect produces [`Event`]s carrying unparsed [`Token`]s, [`FromToken`]
//! turns one token into a domain value, [`FromEvents`] constructs a value from
//! a whole stream, and [`ToEvents`] emits a value without first allocating an
//! [`SExpr`].
//!
//! # Atoms are productions, not one string
//!
//! A dialect reports *which* lexical production produced an atom, and hands
//! over the source spelling rather than an interpretation of it. Matching on
//! [`Token`] is convenient, but a dialect that gains a production gains a
//! variant. [`FromToken`] is the extensible face of the same information: new
//! productions arrive as provided methods, so existing implementations keep
//! compiling and simply reject what they do not model.

use std::borrow::Cow;
use std::convert::Infallible;
use std::fmt;

use crate::{SExpr, SNode, SView, Symbol};

/// A lexical production that can appear in atom position.
///
/// Dialects share this vocabulary so that a [`FromToken`] implementation can
/// be reused across them. New productions may be added, so callers must not
/// assume the listed set is complete.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Production {
    /// An identifier-like atom.
    Symbol,
    /// A numeric literal.
    Number,
    /// A quoted literal denoting text.
    String,
    /// A quoted literal denoting bytes.
    Bytes,
}

impl Production {
    /// Returns the production's name as it appears in diagnostics.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Symbol => "symbol",
            Self::Number => "number",
            Self::String => "string",
            Self::Bytes => "bytes",
        }
    }
}

impl fmt::Display for Production {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// A quoted literal: its source spelling and its decoded value.
///
/// Both halves are kept because both are load-bearing. `raw` is what a
/// re-serializer or span-tracking front end needs; `value` is what a consumer
/// needs. Decoding happens once, while scanning, so escape errors carry a byte
/// offset and a literal without escapes borrows from the input.
pub struct Literal<'a, T: ?Sized + ToOwned> {
    raw: &'a str,
    value: Cow<'a, T>,
}

/// A text literal and its decoded contents.
pub type StrLit<'a> = Literal<'a, str>;

/// A byte-string literal and its decoded contents.
pub type BytesLit<'a> = Literal<'a, [u8]>;

impl<'a, T: ?Sized + ToOwned> Literal<'a, T> {
    /// Pairs a source spelling with its decoded value.
    ///
    /// `raw` excludes the delimiters that introduced the literal.
    pub fn new(raw: &'a str, value: impl Into<Cow<'a, T>>) -> Self {
        Self {
            raw,
            value: value.into(),
        }
    }

    /// Returns the literal's source spelling, without its delimiters.
    #[must_use]
    pub const fn raw(&self) -> &'a str {
        self.raw
    }

    /// Borrows the decoded value.
    #[must_use]
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Returns the decoded value, borrowing when no escape required a copy.
    #[must_use]
    pub fn into_value(self) -> Cow<'a, T> {
        self.value
    }
}

impl<T: ?Sized + ToOwned> Clone for Literal<'_, T> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw,
            value: self.value.clone(),
        }
    }
}

impl<T: ?Sized + ToOwned + fmt::Debug> fmt::Debug for Literal<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Literal")
            .field("raw", &self.raw)
            .field("value", &&*self.value)
            .finish()
    }
}

impl<T: ?Sized + ToOwned + PartialEq> PartialEq for Literal<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw && *self.value == *other.value
    }
}

impl<T: ?Sized + ToOwned + Eq> Eq for Literal<'_, T> {}

/// One unparsed atom token.
///
/// Prefer [`Token::build`] over matching: it routes each production through
/// [`FromToken`], so code keeps compiling when a dialect gains a production.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Token<'a> {
    /// An identifier-like atom, spelled exactly as written.
    Symbol(&'a str),
    /// A numeric literal, spelled exactly as written and not yet evaluated.
    Number(&'a str),
    /// A text literal.
    String(StrLit<'a>),
    /// A byte-string literal.
    Bytes(BytesLit<'a>),
}

impl<'a> Token<'a> {
    /// Returns the production that produced this token.
    #[must_use]
    pub const fn production(&self) -> Production {
        match self {
            Self::Symbol(_) => Production::Symbol,
            Self::Number(_) => Production::Number,
            Self::String(_) => Production::String,
            Self::Bytes(_) => Production::Bytes,
        }
    }

    /// Returns the token's source spelling, without any literal delimiters.
    #[must_use]
    pub const fn raw(&self) -> &'a str {
        match self {
            Self::Symbol(raw) | Self::Number(raw) => raw,
            Self::String(literal) => literal.raw(),
            Self::Bytes(literal) => literal.raw(),
        }
    }

    /// Builds a domain value by dispatching to this token's production.
    ///
    /// # Errors
    ///
    /// Returns `A`'s error, including when `A` does not model the production.
    pub fn build<A: FromToken<'a>>(self) -> Result<A, A::Error> {
        match self {
            Self::Symbol(raw) => A::from_symbol(raw),
            Self::Number(raw) => A::from_number(raw),
            Self::String(literal) => A::from_string(literal),
            Self::Bytes(literal) => A::from_bytes(literal),
        }
    }
}

/// A destination type rejected a production it does not represent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported {
    production: Production,
}

impl Unsupported {
    /// Records that `production` has no representation in the target type.
    #[must_use]
    pub const fn new(production: Production) -> Self {
        Self { production }
    }

    /// Returns the rejected production.
    #[must_use]
    pub const fn production(self) -> Production {
        self.production
    }
}

impl fmt::Display for Unsupported {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "unsupported {} atom", self.production)
    }
}

impl std::error::Error for Unsupported {}

/// Builds a value from one unparsed atom token.
///
/// Each production has its own constructor and receives the source spelling,
/// so an implementation picks its own interpretation: a numeric tower, an
/// interned symbol, or the text itself. Nothing here evaluates a number or
/// resolves a symbol.
///
/// [`from_symbol`], [`from_number`], and [`from_string`] are required because
/// every dialect in this crate emits them. Productions that only some dialects
/// emit are provided methods that reject the token, so adding one is not a
/// breaking change for existing implementations.
///
/// [`from_symbol`]: FromToken::from_symbol
/// [`from_number`]: FromToken::from_number
/// [`from_string`]: FromToken::from_string
pub trait FromToken<'a>: Sized {
    /// The construction error.
    ///
    /// The [`From<Unsupported>`] bound lets provided methods reject a
    /// production without the implementation writing that arm itself.
    type Error: From<Unsupported>;

    /// Builds a value from a symbol's exact spelling.
    ///
    /// # Errors
    ///
    /// Returns an implementation-defined validation error.
    fn from_symbol(raw: &'a str) -> Result<Self, Self::Error>;

    /// Builds a value from a numeric literal's exact spelling.
    ///
    /// The dialect has already checked that `raw` is well-formed for its
    /// grammar; converting it to a numeric type is this method's business.
    ///
    /// # Errors
    ///
    /// Returns an implementation-defined conversion or range error.
    fn from_number(raw: &'a str) -> Result<Self, Self::Error>;

    /// Builds a value from a text literal.
    ///
    /// # Errors
    ///
    /// Returns an implementation-defined validation error.
    fn from_string(literal: StrLit<'a>) -> Result<Self, Self::Error>;

    /// Builds a value from a byte-string literal.
    ///
    /// Defaults to rejecting the production.
    ///
    /// # Errors
    ///
    /// Returns [`Unsupported`] unless overridden.
    fn from_bytes(literal: BytesLit<'a>) -> Result<Self, Self::Error> {
        let _ = literal;
        Err(Unsupported::new(Production::Bytes).into())
    }
}

impl<'a> FromToken<'a> for Token<'a> {
    type Error = Unsupported;

    fn from_symbol(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::Symbol(raw))
    }

    fn from_number(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::Number(raw))
    }

    fn from_string(literal: StrLit<'a>) -> Result<Self, Unsupported> {
        Ok(Self::String(literal))
    }

    fn from_bytes(literal: BytesLit<'a>) -> Result<Self, Unsupported> {
        Ok(Self::Bytes(literal))
    }
}

/// The default owned atom: decoded contents tagged with their production.
///
/// This type keeps a number as the text that was written. Deferring the
/// numeric tower keeps the crate free of a choice that belongs to a domain:
/// implement [`FromToken`] for a domain type to evaluate numbers instead.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Atom {
    /// An identifier-like atom.
    Symbol(Symbol),
    /// A numeric literal, kept as written.
    Number(Symbol),
    /// The decoded contents of a text literal.
    String(Symbol),
    /// The decoded contents of a byte-string literal.
    Bytes(Vec<u8>),
}

impl Atom {
    /// Returns the production that produced this atom.
    #[must_use]
    pub const fn production(&self) -> Production {
        match self {
            Self::Symbol(_) => Production::Symbol,
            Self::Number(_) => Production::Number,
            Self::String(_) => Production::String,
            Self::Bytes(_) => Production::Bytes,
        }
    }

    /// Borrows the atom's text, or returns `None` for a byte string.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Symbol(text) | Self::Number(text) | Self::String(text) => Some(text.as_str()),
            Self::Bytes(_) => None,
        }
    }
}

impl<'a> FromToken<'a> for Atom {
    type Error = Unsupported;

    fn from_symbol(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::Symbol(Symbol::new(raw)))
    }

    fn from_number(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::Number(Symbol::new(raw)))
    }

    fn from_string(literal: StrLit<'a>) -> Result<Self, Unsupported> {
        Ok(Self::String(Symbol::new(literal.value())))
    }

    fn from_bytes(literal: BytesLit<'a>) -> Result<Self, Unsupported> {
        Ok(Self::Bytes(literal.into_value().into_owned()))
    }
}

/// Flattens every text-bearing production to its contents.
///
/// This is the representation to pick when a consumer wants one string per
/// atom and treats spelling differences as insignificant. Byte strings are
/// rejected because they need not be UTF-8.
impl<'a> FromToken<'a> for Symbol {
    type Error = Unsupported;

    fn from_symbol(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::new(raw))
    }

    fn from_number(raw: &'a str) -> Result<Self, Unsupported> {
        Ok(Self::new(raw))
    }

    fn from_string(literal: StrLit<'a>) -> Result<Self, Unsupported> {
        Ok(Self::new(literal.value()))
    }
}

/// One event in a depth-first S-expression stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Event<A = Atom> {
    /// Begin a list.
    ListStart,
    /// An atom.
    Atom(A),
    /// End the most recently opened list.
    ListEnd,
}

impl<A> Event<A> {
    /// Maps the atom while preserving structural events.
    pub fn map<B>(self, map: impl FnOnce(A) -> B) -> Event<B> {
        match self {
            Self::ListStart => Event::ListStart,
            Self::Atom(atom) => Event::Atom(map(atom)),
            Self::ListEnd => Event::ListEnd,
        }
    }

    /// Maps the atom with a fallible function.
    ///
    /// # Errors
    ///
    /// Returns `map`'s error for an atom event.
    pub fn try_map<B, E>(self, map: impl FnOnce(A) -> Result<B, E>) -> Result<Event<B>, E> {
        Ok(match self {
            Self::ListStart => Event::ListStart,
            Self::Atom(atom) => Event::Atom(map(atom)?),
            Self::ListEnd => Event::ListEnd,
        })
    }

    /// Borrows this event's atom.
    #[must_use]
    pub const fn as_ref(&self) -> Event<&A> {
        match self {
            Self::ListStart => Event::ListStart,
            Self::Atom(atom) => Event::Atom(atom),
            Self::ListEnd => Event::ListEnd,
        }
    }
}

impl<'a> Event<Token<'a>> {
    /// Builds this event's atom through [`FromToken`].
    ///
    /// # Errors
    ///
    /// Returns `A`'s error for an atom event.
    pub fn build<A: FromToken<'a>>(self) -> Result<Event<A>, A::Error> {
        self.try_map(Token::build)
    }
}

/// A fallible destination for borrowed SAX events.
///
/// Implementations can write a wire format, feed another state machine, or
/// simply collect events for testing.
pub trait EventWriter<A: ?Sized = Atom> {
    /// The write error.
    type Error;

    /// Accepts one event.
    ///
    /// # Errors
    ///
    /// Returns the destination's error if it cannot accept the event.
    fn write(&mut self, event: Event<&A>) -> Result<(), Self::Error>;
}

impl<A: ?Sized, F, E> EventWriter<A> for F
where
    F: FnMut(Event<&A>) -> Result<(), E>,
{
    type Error = E;

    fn write(&mut self, event: Event<&A>) -> Result<(), E> {
        self(event)
    }
}

/// A value that can emit its S-expression representation as SAX events.
pub trait ToEvents {
    /// The atom representation borrowed during emission.
    type Atom: ?Sized;

    /// Emits a complete, balanced expression.
    ///
    /// # Errors
    ///
    /// Returns the writer's error and stops emitting.
    fn write_events<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: EventWriter<Self::Atom>;
}

impl<A> ToEvents for SExpr<A> {
    type Atom = A;

    fn write_events<W>(&self, writer: &mut W) -> Result<(), W::Error>
    where
        W: EventWriter<A>,
    {
        write_view(self, writer)
    }
}

/// Emits any structural view in depth-first order.
///
/// # Errors
///
/// Returns the writer's error and stops traversing.
pub fn write_view<V, W>(value: V, writer: &mut W) -> Result<(), W::Error>
where
    V: SView,
    W: EventWriter<V::Atom>,
{
    match value.view() {
        SNode::Atom(atom) => writer.write(Event::Atom(atom)),
        SNode::List(children) => {
            writer.write(Event::ListStart)?;
            for child in children {
                write_view(child, writer)?;
            }
            writer.write(Event::ListEnd)
        }
    }
}

/// A type constructible from one complete SAX expression.
///
/// Implementations own validation and resource policy. In particular, a domain
/// type need not construct an [`SExpr`] first.
pub trait FromEvents<A = Atom>: Sized {
    /// The construction error.
    type Error;

    /// Consumes exactly one complete expression.
    ///
    /// # Errors
    ///
    /// Returns an implementation-defined validation or construction error.
    fn from_events(events: impl IntoIterator<Item = Event<A>>) -> Result<Self, Self::Error>;
}

/// Structural errors while constructing an owned [`SExpr`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// The stream contained no expression.
    Empty,
    /// The stream contained more than one top-level expression.
    MultipleRoots,
    /// A list end had no matching list start.
    UnexpectedListEnd,
    /// The stream ended with one or more open lists.
    UnclosedList,
}

impl fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::Empty => "event stream contains no expression",
            Self::MultipleRoots => "event stream contains multiple top-level expressions",
            Self::UnexpectedListEnd => "list end has no matching list start",
            Self::UnclosedList => "event stream ends inside a list",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for BuildError {}

impl<A> FromEvents<A> for SExpr<A> {
    type Error = BuildError;

    fn from_events(events: impl IntoIterator<Item = Event<A>>) -> Result<Self, Self::Error> {
        let mut stack: Vec<Vec<Self>> = Vec::new();
        let mut root = None;

        for event in events {
            let completed = match event {
                Event::ListStart => {
                    stack.push(Vec::new());
                    continue;
                }
                Event::Atom(atom) => Self::Atom(atom),
                Event::ListEnd => {
                    let children = stack.pop().ok_or(BuildError::UnexpectedListEnd)?;
                    Self::List(children)
                }
            };

            if let Some(parent) = stack.last_mut() {
                parent.push(completed);
            } else if root.replace(completed).is_some() {
                return Err(BuildError::MultipleRoots);
            }
        }

        if !stack.is_empty() {
            return Err(BuildError::UnclosedList);
        }
        root.ok_or(BuildError::Empty)
    }
}

/// Collects emitted atoms by cloning them.
///
/// This is useful at ownership boundaries and in tests; streaming consumers
/// should implement [`EventWriter`] directly.
pub fn collect_events<T>(value: &T) -> Vec<Event<T::Atom>>
where
    T: ToEvents,
    T::Atom: Clone + Sized,
{
    let mut events = Vec::new();
    let mut writer = |event: Event<&T::Atom>| -> Result<(), Infallible> {
        events.push(event.map(Clone::clone));
        Ok(())
    };
    match value.write_events(&mut writer) {
        Ok(()) => events,
        Err(error) => match error {},
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Atom, BuildError, Event, FromEvents, FromToken, Production, StrLit, Token, Unsupported,
        collect_events,
    };
    use crate::{SExpr, Symbol};

    #[test]
    fn owned_tree_round_trips_through_events() {
        let expression = SExpr::list(vec![
            SExpr::atom(String::from("a")),
            SExpr::list(vec![]),
            SExpr::atom(String::from("b")),
        ]);
        let events = collect_events(&expression);
        assert_eq!(SExpr::from_events(events), Ok(expression));
    }

    #[test]
    fn builder_rejects_invalid_structure() {
        assert_eq!(SExpr::<String>::from_events([]), Err(BuildError::Empty));
        assert_eq!(
            SExpr::<String>::from_events([Event::ListEnd]),
            Err(BuildError::UnexpectedListEnd)
        );
        assert_eq!(
            SExpr::from_events([Event::Atom("a"), Event::Atom("b")]),
            Err(BuildError::MultipleRoots)
        );
        assert_eq!(
            SExpr::<String>::from_events([Event::ListStart]),
            Err(BuildError::UnclosedList)
        );
    }

    #[test]
    fn tokens_keep_their_production_and_spelling() {
        assert_eq!(Token::Number("007").production(), Production::Number);
        assert_eq!(Token::Number("007").raw(), "007");

        let literal = StrLit::new("a\\nb", String::from("a\nb"));
        assert_eq!(literal.raw(), "a\\nb");
        assert_eq!(literal.value(), "a\nb");
        assert_eq!(Token::String(literal).production(), Production::String);
    }

    #[test]
    fn build_dispatches_each_production_separately() {
        assert_eq!(
            Token::Symbol("x").build::<Atom>(),
            Ok(Atom::Symbol(Symbol::new("x")))
        );
        // A number keeps its spelling rather than becoming a numeric value.
        assert_eq!(
            Token::Number("1e3").build::<Atom>(),
            Ok(Atom::Number(Symbol::new("1e3")))
        );
        assert_eq!(
            Token::String(StrLit::new("hi", "hi")).build::<Atom>(),
            Ok(Atom::String(Symbol::new("hi")))
        );
    }

    #[test]
    fn symbol_flattens_text_and_rejects_bytes() {
        assert_eq!(Token::Number("42").build::<Symbol>(), Ok(Symbol::new("42")));
        assert_eq!(
            Token::Bytes(super::BytesLit::new("a", b"a".as_slice())).build::<Symbol>(),
            Err(Unsupported::new(Production::Bytes))
        );
    }

    /// A domain type that models only what it needs, using the provided
    /// method to reject the rest.
    #[derive(Debug, PartialEq)]
    enum Count {
        Value(u32),
    }

    impl FromToken<'_> for Count {
        type Error = Unsupported;

        fn from_symbol(_: &str) -> Result<Self, Unsupported> {
            Err(Unsupported::new(Production::Symbol))
        }

        fn from_number(raw: &str) -> Result<Self, Unsupported> {
            raw.parse()
                .map(Count::Value)
                .map_err(|_| Unsupported::new(Production::Number))
        }

        fn from_string(_: StrLit<'_>) -> Result<Self, Unsupported> {
            Err(Unsupported::new(Production::String))
        }
    }

    #[test]
    fn a_domain_type_selects_the_productions_it_models() {
        assert_eq!(Token::Number("7").build::<Count>(), Ok(Count::Value(7)));
        assert_eq!(
            Token::Symbol("seven").build::<Count>(),
            Err(Unsupported::new(Production::Symbol))
        );
        // `from_bytes` was never written, yet the type still compiles and
        // rejects the production it does not model.
        assert_eq!(
            Token::Bytes(super::BytesLit::new("", b"".as_slice())).build::<Count>(),
            Err(Unsupported::new(Production::Bytes))
        );
    }
}
