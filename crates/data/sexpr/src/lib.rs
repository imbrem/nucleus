//! Owned S-expression values and an iterative event reader.
//!
//! This crate only recognizes syntax. Directives and all other atoms are inert
//! data until a userspace interpreter assigns them meaning.

use std::iter::FusedIterator;
use std::ops::Range;

use bytes::Bytes;
use covalence_lib_error::snafu::Snafu;
use smol_str::SmolStr;

/// A half-open UTF-8 byte range in the source document.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Span {
    /// First byte in the range.
    pub start: usize,
    /// First byte after the range.
    pub end: usize,
}

impl Span {
    /// Creates a span from a half-open byte range.
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Returns the corresponding standard range.
    #[must_use]
    pub const fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// An owned atomic S-expression value.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Atom {
    /// An ordinary identifier.
    Symbol(SmolStr),
    /// Decoded quoted text.
    String(SmolStr),
    /// Decoded binary-literal bytes.
    Bytes(Bytes),
    /// An exact spelling whose first byte is an ASCII digit.
    Number(SmolStr),
    /// A colon-prefixed name, stored without its colon.
    Keyword(SmolStr),
    /// A hash-prefixed primitive name, stored without its hash.
    Directive(SmolStr),
}

impl Atom {
    /// Encodes bytes using the canonical byte-literal spelling.
    #[must_use]
    pub fn encode_bytes(bytes: &[u8]) -> String {
        let mut encoded = String::from("b\"");
        for &byte in bytes {
            match byte {
                b'\\' => encoded.push_str("\\\\"),
                b'"' => encoded.push_str("\\\""),
                b'\n' => encoded.push_str("\\n"),
                b'\r' => encoded.push_str("\\r"),
                b'\t' => encoded.push_str("\\t"),
                0 => encoded.push_str("\\0"),
                0x20..=0x7e => encoded.push(char::from(byte)),
                _ => {
                    use std::fmt::Write as _;
                    write!(encoded, "\\x{byte:02x}").expect("writing to a string cannot fail");
                }
            }
        }
        encoded.push('"');
        encoded
    }
}

/// One structural parser or traversal event.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Event {
    /// The opening parenthesis of a proper list.
    Open { span: Span },
    /// An atomic value.
    Atom { value: Atom, span: Span },
    /// The closing parenthesis of a proper list.
    Close { span: Span },
}

/// Why textual input could not be read.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ParseError {
    /// A closing parenthesis had no corresponding opening parenthesis.
    #[snafu(display("unexpected closing parenthesis at byte {}", span.start))]
    UnexpectedClose {
        /// Location of the closing parenthesis.
        span: Span,
    },
    /// Input ended while one or more lists remained open.
    #[snafu(display("unterminated list at byte {}", span.start))]
    UnterminatedList {
        /// Empty span at the end of input.
        span: Span,
    },
    /// Input ended before a string's closing quote.
    #[snafu(display("unterminated string beginning at byte {}", span.start))]
    UnterminatedString {
        /// Source from the opening quote through the end of input.
        span: Span,
    },
    /// A string contained an unsupported escape.
    #[snafu(display("invalid string escape at byte {}", span.start))]
    InvalidEscape {
        /// Location of the backslash and escaped character, if present.
        span: Span,
    },
    /// A keyword had no name.
    #[snafu(display("empty keyword at byte {}", span.start))]
    EmptyKeyword {
        /// Location of the colon.
        span: Span,
    },
    /// A directive had no name.
    #[snafu(display("empty directive at byte {}", span.start))]
    EmptyDirective {
        /// Location of the hash.
        span: Span,
    },
    /// A byte literal contained invalid source text or an invalid escape.
    #[snafu(display("invalid byte literal at byte {}", span.start))]
    InvalidBytes {
        /// Location of the complete literal, or its remaining input.
        span: Span,
    },
    /// A parser implementation produced an unbalanced event stream.
    #[snafu(display("parser produced an invalid event stream: {source}"))]
    Structure {
        /// Structural event-stream error.
        source: StructureError,
    },
}

/// A non-recursive event reader over UTF-8 text.
///
/// Events borrow no source data. The iterator has no nesting limit; callers
/// may impose their own event or byte budgets.
#[derive(Clone, Debug)]
pub struct Parser<'a> {
    input: &'a str,
    offset: usize,
    depth: usize,
    done: bool,
}

impl<'a> Parser<'a> {
    /// Creates an event reader.
    #[must_use]
    pub const fn new(input: &'a str) -> Self {
        Self {
            input,
            offset: 0,
            depth: 0,
            done: false,
        }
    }

    fn skip_trivia(&mut self) {
        loop {
            let rest = &self.input[self.offset..];
            let mut advanced = 0;
            for character in rest.chars() {
                if character.is_whitespace() {
                    advanced += character.len_utf8();
                } else {
                    break;
                }
            }
            self.offset += advanced;
            if self.input.as_bytes().get(self.offset) != Some(&b';') {
                return;
            }
            self.offset += self.input[self.offset..]
                .find('\n')
                .unwrap_or(self.input.len() - self.offset);
        }
    }

    fn quoted(&mut self, start: usize) -> Result<(SmolStr, Span), ParseError> {
        debug_assert_eq!(self.input.as_bytes()[self.offset], b'"');
        self.offset += 1;
        let mut decoded = String::new();
        loop {
            let Some(character) = self.input[self.offset..].chars().next() else {
                return Err(ParseError::UnterminatedString {
                    span: Span::new(start, self.input.len()),
                });
            };
            let character_start = self.offset;
            self.offset += character.len_utf8();
            match character {
                '"' => return Ok((decoded.into(), Span::new(start, self.offset))),
                '\\' => {
                    let Some(escaped) = self.input[self.offset..].chars().next() else {
                        return Err(ParseError::InvalidEscape {
                            span: Span::new(character_start, self.offset),
                        });
                    };
                    self.offset += escaped.len_utf8();
                    decoded.push(match escaped {
                        '"' => '"',
                        '\\' => '\\',
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        '0' => '\0',
                        _ => {
                            return Err(ParseError::InvalidEscape {
                                span: Span::new(character_start, self.offset),
                            });
                        }
                    });
                }
                other => decoded.push(other),
            }
        }
    }

    fn bytes(&mut self, start: usize) -> Result<(Bytes, Span), ParseError> {
        debug_assert!(self.input[self.offset..].starts_with("b\""));
        self.offset += 2;
        let mut decoded = Vec::new();
        loop {
            let Some(&byte) = self.input.as_bytes().get(self.offset) else {
                return Err(ParseError::UnterminatedString {
                    span: Span::new(start, self.input.len()),
                });
            };
            match byte {
                b'"' => {
                    self.offset += 1;
                    return Ok((Bytes::from(decoded), Span::new(start, self.offset)));
                }
                b'\\' => {
                    let escape_start = self.offset;
                    self.offset += 1;
                    let Some(&escaped) = self.input.as_bytes().get(self.offset) else {
                        return Err(ParseError::InvalidBytes {
                            span: Span::new(escape_start, self.offset),
                        });
                    };
                    self.offset += 1;
                    match escaped {
                        b'\\' => decoded.push(b'\\'),
                        b'"' => decoded.push(b'"'),
                        b'n' => decoded.push(b'\n'),
                        b'r' => decoded.push(b'\r'),
                        b't' => decoded.push(b'\t'),
                        b'0' => decoded.push(0),
                        b'x' => {
                            let hex_start = self.offset;
                            let hex_end = hex_start.saturating_add(2);
                            let Some(hex) = self.input.get(hex_start..hex_end) else {
                                return Err(ParseError::InvalidBytes {
                                    span: Span::new(escape_start, self.input.len()),
                                });
                            };
                            if !hex.as_bytes().iter().all(u8::is_ascii_hexdigit) {
                                return Err(ParseError::InvalidBytes {
                                    span: Span::new(escape_start, hex_end),
                                });
                            }
                            decoded.push(u8::from_str_radix(hex, 16).map_err(|_| {
                                ParseError::InvalidBytes {
                                    span: Span::new(escape_start, hex_end),
                                }
                            })?);
                            self.offset = hex_end;
                        }
                        _ => {
                            return Err(ParseError::InvalidBytes {
                                span: Span::new(escape_start, self.offset),
                            });
                        }
                    }
                }
                0x20..=0x7e => {
                    decoded.push(byte);
                    self.offset += 1;
                }
                _ => {
                    let end = self.offset
                        + self.input[self.offset..]
                            .chars()
                            .next()
                            .map_or(1, char::len_utf8);
                    return Err(ParseError::InvalidBytes {
                        span: Span::new(self.offset, end),
                    });
                }
            }
        }
    }

    fn bare_end(&self) -> usize {
        self.input[self.offset..]
            .char_indices()
            .find_map(|(index, character)| {
                (character.is_whitespace() || matches!(character, '(' | ')' | ';'))
                    .then_some(self.offset + index)
            })
            .unwrap_or(self.input.len())
    }

    fn atom(&mut self) -> Result<Event, ParseError> {
        let start = self.offset;
        if self.input[start..].starts_with("b\"") {
            let (value, span) = self.bytes(start)?;
            return Ok(Event::Atom {
                value: Atom::Bytes(value),
                span,
            });
        }
        if self.input.as_bytes()[start] == b'"' {
            let (value, span) = self.quoted(start)?;
            return Ok(Event::Atom {
                value: Atom::String(value),
                span,
            });
        }
        let end = self.bare_end();
        self.offset = end;
        let spelling = &self.input[start..end];
        let span = Span::new(start, end);
        let value = if let Some(name) = spelling.strip_prefix(':') {
            if name.is_empty() {
                return Err(ParseError::EmptyKeyword { span });
            }
            Atom::Keyword(name.into())
        } else if let Some(name) = spelling.strip_prefix('#') {
            if name.is_empty() {
                return Err(ParseError::EmptyDirective { span });
            }
            Atom::Directive(name.into())
        } else if spelling.as_bytes()[0].is_ascii_digit() {
            Atom::Number(spelling.into())
        } else {
            Atom::Symbol(spelling.into())
        };
        Ok(Event::Atom { value, span })
    }
}

impl Iterator for Parser<'_> {
    type Item = Result<Event, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        self.skip_trivia();
        let Some(&byte) = self.input.as_bytes().get(self.offset) else {
            self.done = true;
            return (self.depth != 0).then(|| {
                Err(ParseError::UnterminatedList {
                    span: Span::new(self.offset, self.offset),
                })
            });
        };
        match byte {
            b'(' => {
                let span = Span::new(self.offset, self.offset + 1);
                self.offset += 1;
                self.depth += 1;
                Some(Ok(Event::Open { span }))
            }
            b')' if self.depth == 0 => {
                let span = Span::new(self.offset, self.offset + 1);
                self.done = true;
                Some(Err(ParseError::UnexpectedClose { span }))
            }
            b')' => {
                let span = Span::new(self.offset, self.offset + 1);
                self.offset += 1;
                self.depth -= 1;
                Some(Ok(Event::Close { span }))
            }
            _ => match self.atom() {
                Ok(event) => Some(Ok(event)),
                Err(error) => {
                    self.done = true;
                    Some(Err(error))
                }
            },
        }
    }
}

impl FusedIterator for Parser<'_> {}

/// An owned S-expression.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Expr {
    /// An atomic value and its source span.
    Atom { value: Atom, span: Span },
    /// A proper list. Delimiter spans are retained independently.
    List {
        open: Span,
        items: Box<[Self]>,
        close: Span,
    },
}

impl Expr {
    /// Traverses this expression as a balanced event stream without recursion.
    #[must_use]
    pub fn events(&self) -> Events<'_> {
        Events::expression(self)
    }
}

/// An owned sequence of top-level expressions.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Document {
    expressions: Box<[Expr]>,
}

impl Document {
    /// Creates a document from top-level expressions.
    #[must_use]
    pub fn new(expressions: impl Into<Box<[Expr]>>) -> Self {
        Self {
            expressions: expressions.into(),
        }
    }

    /// Returns the top-level expressions.
    #[must_use]
    pub const fn expressions(&self) -> &[Expr] {
        &self.expressions
    }

    /// Traverses this document as an event stream without recursion.
    #[must_use]
    pub fn events(&self) -> Events<'_> {
        Events::document(self)
    }

    /// Folds a structural event stream into an owned document without recursion.
    ///
    /// # Errors
    ///
    /// Returns an error when closing delimiters are unmatched or the stream
    /// ends with an unclosed list.
    pub fn from_events(events: impl IntoIterator<Item = Event>) -> Result<Self, StructureError> {
        struct Frame {
            open: Span,
            items: Vec<Expr>,
        }
        let mut roots = Vec::new();
        let mut frames: Vec<Frame> = Vec::new();
        for event in events {
            let expression = match event {
                Event::Open { span } => {
                    frames.push(Frame {
                        open: span,
                        items: Vec::new(),
                    });
                    continue;
                }
                Event::Atom { value, span } => Expr::Atom { value, span },
                Event::Close { span } => {
                    let Some(frame) = frames.pop() else {
                        return Err(StructureError::UnexpectedCloseEvent { span });
                    };
                    Expr::List {
                        open: frame.open,
                        items: frame.items.into_boxed_slice(),
                        close: span,
                    }
                }
            };
            if let Some(frame) = frames.last_mut() {
                frame.items.push(expression);
            } else {
                roots.push(expression);
            }
        }
        if let Some(frame) = frames.first() {
            return Err(StructureError::UnterminatedListEvents { open: frame.open });
        }
        Ok(Self::new(roots))
    }
}

/// Why an externally supplied event stream was not balanced.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum StructureError {
    /// A close event had no open event.
    #[snafu(display("unexpected close event at byte {}", span.start))]
    UnexpectedCloseEvent {
        /// Location associated with the close event.
        span: Span,
    },
    /// The stream ended while a list remained open.
    #[snafu(display("unterminated list event opened at byte {}", open.start))]
    UnterminatedListEvents {
        /// Location associated with the first unclosed open event.
        open: Span,
    },
}

#[derive(Debug)]
enum Pending<'a> {
    Expr(&'a Expr),
    Close(Span),
}

/// A non-recursive AST traversal.
#[derive(Debug)]
pub struct Events<'a> {
    pending: Vec<Pending<'a>>,
}

impl<'a> Events<'a> {
    fn expression(expression: &'a Expr) -> Self {
        Self {
            pending: vec![Pending::Expr(expression)],
        }
    }

    fn document(document: &'a Document) -> Self {
        Self {
            pending: document
                .expressions
                .iter()
                .rev()
                .map(Pending::Expr)
                .collect(),
        }
    }
}

impl Iterator for Events<'_> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pending.pop()? {
            Pending::Close(span) => Some(Event::Close { span }),
            Pending::Expr(Expr::Atom { value, span }) => Some(Event::Atom {
                value: value.clone(),
                span: *span,
            }),
            Pending::Expr(Expr::List { open, items, close }) => {
                self.pending.push(Pending::Close(*close));
                self.pending.extend(items.iter().rev().map(Pending::Expr));
                Some(Event::Open { span: *open })
            }
        }
    }
}

impl FusedIterator for Events<'_> {}

/// Parses a complete document into an owned AST.
///
/// # Errors
///
/// Returns [`ParseError`] for malformed text. The parser itself guarantees a
/// balanced stream, so construction cannot produce a [`StructureError`].
pub fn parse(input: &str) -> Result<Document, ParseError> {
    let events = Parser::new(input).collect::<Result<Vec<_>, _>>()?;
    Document::from_events(events).map_err(|source| ParseError::Structure { source })
}

/// Parses exactly one top-level expression.
///
/// # Errors
///
/// Returns [`OneError::Parse`] for malformed text and [`OneError::Count`] when
/// the document does not contain exactly one expression.
pub fn parse_one(input: &str) -> Result<Expr, OneError> {
    let document = parse(input).map_err(|source| OneError::Parse { source })?;
    let expressions = document.expressions.into_vec();
    let actual = expressions.len();
    if actual != 1 {
        return Err(OneError::Count { actual });
    }
    expressions
        .into_iter()
        .next()
        .ok_or(OneError::Count { actual })
}

/// Why text did not contain exactly one expression.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum OneError {
    /// The document was malformed.
    #[snafu(display("could not parse expression: {source}"))]
    Parse {
        /// Underlying reader error.
        source: ParseError,
    },
    /// The document contained the wrong number of roots.
    #[snafu(display("expected one expression, found {actual}"))]
    Count {
        /// Number of top-level expressions.
        actual: usize,
    },
}
