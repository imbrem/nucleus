//! Dialect-driven textual parsing.
//!
//! Every S-expression syntax in practice agrees on parentheses and disagrees
//! about everything else: what counts as whitespace, how comments are spelled,
//! which atoms are numbers, and what a quoted literal decodes to. [`Dialect`]
//! isolates exactly those disagreements, so [`Parser`] implements the shared
//! structure once.
//!
//! A dialect never sees `(` or `)`: it reports trivia and scans one atom at a
//! time, and the parser owns nesting, balance, and end-of-input handling.

use std::fmt;

use crate::SExpr;
use crate::sax::{BuildError, Event, FromToken, Token};

/// A text syntax error with its UTF-8 byte offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    offset: usize,
    kind: ErrorKind,
}

/// The category of a text syntax error.
///
/// Dialects share this vocabulary; new categories may be added.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorKind {
    /// A closing parenthesis has no matching opening parenthesis.
    UnexpectedListEnd,
    /// Input ended with open lists.
    UnclosedList,
    /// Input ended inside a quoted literal.
    UnterminatedLiteral,
    /// Input ended inside a block comment.
    UnterminatedComment,
    /// A quoted literal contains an escape the dialect does not define.
    InvalidEscape,
    /// A quoted literal contains a character the dialect requires be escaped.
    InvalidCharacter,
    /// An atom begins like a number but is not one in this dialect.
    InvalidNumber,
    /// An atom is not a symbol in this dialect.
    InvalidSymbol,
}

impl ErrorKind {
    /// Returns a human-readable description of this category.
    #[must_use]
    pub const fn message(self) -> &'static str {
        match self {
            Self::UnexpectedListEnd => "closing parenthesis has no matching opening parenthesis",
            Self::UnclosedList => "input ends inside a list",
            Self::UnterminatedLiteral => "input ends inside a quoted literal",
            Self::UnterminatedComment => "input ends inside a block comment",
            Self::InvalidEscape => "undefined escape sequence",
            Self::InvalidCharacter => "character must be written as an escape",
            Self::InvalidNumber => "malformed number",
            Self::InvalidSymbol => "malformed symbol",
        }
    }
}

impl Error {
    /// Records a syntax error at `offset`.
    #[must_use]
    pub const fn new(offset: usize, kind: ErrorKind) -> Self {
        Self { offset, kind }
    }

    /// Returns the UTF-8 byte offset where parsing failed.
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the error category.
    #[must_use]
    pub const fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at byte {}", self.kind.message(), self.offset)
    }
}

impl std::error::Error for Error {}

/// A lexical variant of S-expression text.
///
/// Implementations are usually zero-sized. Both methods take the whole input
/// and a byte offset rather than a suffix so that every reported offset is
/// absolute.
pub trait Dialect {
    /// Advances past whitespace and comments starting at `from`.
    ///
    /// Returns the offset of the first byte that is not trivia, which may be
    /// `from` itself or the end of the input.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorKind::UnterminatedComment`] when the input ends inside a
    /// block comment.
    fn skip_trivia(&self, input: &str, from: usize) -> Result<usize, Error>;

    /// Scans one atom beginning at `from`.
    ///
    /// `from` is guaranteed to be a UTF-8 boundary that is neither trivia,
    /// `(`, `)`, nor the end of the input. Returns the token and the offset
    /// just past it.
    ///
    /// # Errors
    ///
    /// Returns a syntax error whose offset lies within the atom.
    fn scan_atom<'a>(&self, input: &'a str, from: usize) -> Result<(Token<'a>, usize), Error>;
}

impl<D: Dialect + ?Sized> Dialect for &D {
    fn skip_trivia(&self, input: &str, from: usize) -> Result<usize, Error> {
        (**self).skip_trivia(input, from)
    }

    fn scan_atom<'a>(&self, input: &'a str, from: usize) -> Result<(Token<'a>, usize), Error> {
        (**self).scan_atom(input, from)
    }
}

/// A streaming parser over UTF-8 S-expression text.
///
/// The iterator yields one [`Event`] at a time and stops permanently after the
/// first error. Atoms borrow from the input unless decoding an escape required
/// a copy.
#[derive(Clone, Debug)]
pub struct Parser<'a, D> {
    input: &'a str,
    dialect: D,
    offset: usize,
    event_offset: usize,
    depth: usize,
    finished: bool,
}

/// Parses `input` in `dialect` into a lazy SAX event stream.
#[must_use]
pub const fn parse<D>(input: &str, dialect: D) -> Parser<'_, D> {
    Parser {
        input,
        dialect,
        offset: 0,
        event_offset: 0,
        depth: 0,
        finished: false,
    }
}

impl<D> Parser<'_, D> {
    /// Returns the byte offset the next event will be scanned from.
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the byte offset where the most recent event began.
    #[must_use]
    pub const fn event_offset(&self) -> usize {
        self.event_offset
    }

    /// Returns the number of lists currently open.
    #[must_use]
    pub const fn depth(&self) -> usize {
        self.depth
    }
}

impl<'a, D: Dialect> Iterator for Parser<'a, D> {
    type Item = Result<Event<Token<'a>>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        self.offset = match self.dialect.skip_trivia(self.input, self.offset) {
            Ok(offset) => offset,
            Err(error) => {
                self.finished = true;
                return Some(Err(error));
            }
        };
        self.event_offset = self.offset;

        if self.offset == self.input.len() {
            self.finished = true;
            return if self.depth == 0 {
                None
            } else {
                Some(Err(Error::new(self.offset, ErrorKind::UnclosedList)))
            };
        }

        match self.input.as_bytes()[self.offset] {
            b'(' => {
                self.offset += 1;
                self.depth += 1;
                Some(Ok(Event::ListStart))
            }
            b')' if self.depth == 0 => {
                self.finished = true;
                Some(Err(Error::new(self.offset, ErrorKind::UnexpectedListEnd)))
            }
            b')' => {
                self.offset += 1;
                self.depth -= 1;
                Some(Ok(Event::ListEnd))
            }
            _ => match self.dialect.scan_atom(self.input, self.offset) {
                Ok((token, end)) => {
                    debug_assert!(end > self.offset, "scan_atom must consume input");
                    self.offset = end;
                    Some(Ok(Event::Atom(token)))
                }
                Err(error) => {
                    self.finished = true;
                    Some(Err(error))
                }
            },
        }
    }
}

/// An error reading text into an owned expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadError<E> {
    /// The input is not valid in the dialect.
    Syntax(Error),
    /// An atom could not be built into the requested representation.
    Token {
        /// The byte offset where the rejected atom began.
        offset: usize,
        /// The representation's error.
        error: E,
    },
    /// The input did not contain exactly one expression.
    Structure(BuildError),
}

impl<E: fmt::Display> fmt::Display for ReadError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax(error) => write!(formatter, "invalid S-expression text: {error}"),
            Self::Token { offset, error } => {
                write!(formatter, "{error} at byte {offset}")
            }
            Self::Structure(error) => write!(formatter, "invalid S-expression structure: {error}"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for ReadError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Syntax(error) => Some(error),
            Self::Token { error, .. } => Some(error),
            Self::Structure(error) => Some(error),
        }
    }
}

/// Reads every top-level expression in `input`.
///
/// # Errors
///
/// Returns syntax, atom-construction, and structural errors without conflating
/// their causes.
pub fn read_all<'a, A, D>(input: &'a str, dialect: D) -> Result<Vec<SExpr<A>>, ReadError<A::Error>>
where
    A: FromToken<'a>,
    D: Dialect,
{
    let mut parser = parse(input, dialect);
    let mut stack: Vec<Vec<SExpr<A>>> = Vec::new();
    let mut roots = Vec::new();

    while let Some(result) = parser.next() {
        let offset = parser.event_offset();
        let value = match result.map_err(ReadError::Syntax)? {
            Event::ListStart => {
                stack.push(Vec::new());
                continue;
            }
            Event::Atom(token) => {
                let atom = token
                    .build()
                    .map_err(|error| ReadError::Token { offset, error })?;
                SExpr::Atom(atom)
            }
            Event::ListEnd => {
                let children = stack
                    .pop()
                    .ok_or(ReadError::Structure(BuildError::UnexpectedListEnd))?;
                SExpr::List(children)
            }
        };

        match stack.last_mut() {
            Some(parent) => parent.push(value),
            None => roots.push(value),
        }
    }

    if stack.is_empty() {
        Ok(roots)
    } else {
        Err(ReadError::Structure(BuildError::UnclosedList))
    }
}

/// Reads exactly one expression from `input`.
///
/// # Errors
///
/// Returns [`BuildError::Empty`] or [`BuildError::MultipleRoots`] when `input`
/// does not hold exactly one expression, plus the errors of [`read_all`].
pub fn read<'a, A, D>(input: &'a str, dialect: D) -> Result<SExpr<A>, ReadError<A::Error>>
where
    A: FromToken<'a>,
    D: Dialect,
{
    let mut roots = read_all(input, dialect)?;
    if roots.len() > 1 {
        return Err(ReadError::Structure(BuildError::MultipleRoots));
    }
    roots.pop().ok_or(ReadError::Structure(BuildError::Empty))
}

#[cfg(test)]
mod tests {
    use super::{ErrorKind, read, read_all};
    use crate::dialect::Pose;
    use crate::sax::{Atom, Event};

    #[test]
    fn a_parser_stops_permanently_after_the_first_error() {
        let mut parser = super::parse("(a)) (b)", Pose);
        assert!(matches!(parser.next(), Some(Ok(Event::ListStart))));
        assert!(parser.next().is_some());
        assert!(matches!(parser.next(), Some(Ok(Event::ListEnd))));

        let error = parser.next().expect("an error").expect_err("unbalanced");
        assert_eq!(error.kind(), ErrorKind::UnexpectedListEnd);
        // Everything after the error is discarded, including the valid `(b)`.
        assert!(parser.next().is_none());
        assert!(parser.next().is_none());
    }

    #[test]
    fn a_parser_tracks_depth_and_offsets_as_it_goes() {
        let mut parser = super::parse("  (a)", Pose);
        assert_eq!(parser.depth(), 0);

        parser.next().expect("list start").expect("valid");
        assert_eq!(parser.event_offset(), 2);
        assert_eq!(parser.depth(), 1);

        parser.next().expect("atom").expect("valid");
        assert_eq!(parser.event_offset(), 3);
        assert_eq!(parser.offset(), 4);

        parser.next().expect("list end").expect("valid");
        assert_eq!(parser.depth(), 0);
        assert!(parser.next().is_none());
    }

    #[test]
    fn empty_and_trivia_only_input_yields_no_roots() {
        assert!(read_all::<Atom, _>("", Pose).expect("valid").is_empty());
        assert!(
            read_all::<Atom, _>("  ; nothing here\n", Pose)
                .expect("valid")
                .is_empty()
        );
    }

    #[test]
    fn a_dialect_may_be_passed_by_reference() {
        assert!(read::<Atom, _>("(a b)", &Pose).is_ok());
    }
}
