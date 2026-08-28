//! Owned S-expression values and an iterative event reader.
//!
//! This crate only recognizes syntax. Directives and all other atoms are inert
//! data until a userspace interpreter assigns them meaning.

use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ops::Range;
use std::sync::Arc;
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
};

use bytes::Bytes;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_lib_pretty::RcDoc;
use smol_str::SmolStr;

/// A half-open UTF-8 byte range in the source document.
pub type Span = Range<u64>;

fn span(start: usize, end: usize) -> Span {
    u64::try_from(start).expect("source offsets fit in u64")
        ..u64::try_from(end).expect("source offsets fit in u64")
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
    /// A canonical 256-bit object address.
    O256(O256),
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

    /// Encodes an address as a parenthesized, canonical padded Base64 atom.
    #[must_use]
    pub fn encode_o256(value: O256) -> String {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let bytes = value.as_ref();
        let mut encoded = String::with_capacity(47);
        encoded.push_str("!(");
        for chunk in bytes.chunks_exact(3) {
            encoded.push(char::from(ALPHABET[usize::from(chunk[0] >> 2)]));
            encoded.push(char::from(
                ALPHABET[usize::from((chunk[0] & 0x03) << 4 | chunk[1] >> 4)],
            ));
            encoded.push(char::from(
                ALPHABET[usize::from((chunk[1] & 0x0f) << 2 | chunk[2] >> 6)],
            ));
            encoded.push(char::from(ALPHABET[usize::from(chunk[2] & 0x3f)]));
        }
        let tail = bytes.chunks_exact(3).remainder();
        debug_assert_eq!(tail.len(), 2);
        encoded.push(char::from(ALPHABET[usize::from(tail[0] >> 2)]));
        encoded.push(char::from(
            ALPHABET[usize::from((tail[0] & 0x03) << 4 | tail[1] >> 4)],
        ));
        encoded.push(char::from(ALPHABET[usize::from((tail[1] & 0x0f) << 2)]));
        encoded.push('=');
        encoded.push(')');
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
    /// An address atom was not canonical padded Base64 for exactly 32 bytes.
    #[snafu(display("invalid O256 literal at byte {}", span.start))]
    InvalidO256 {
        /// Location of the complete address atom, or its remaining input.
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
                    span: span(start, self.input.len()),
                });
            };
            let character_start = self.offset;
            self.offset += character.len_utf8();
            match character {
                '"' => return Ok((decoded.into(), span(start, self.offset))),
                '\\' => {
                    let Some(escaped) = self.input[self.offset..].chars().next() else {
                        return Err(ParseError::InvalidEscape {
                            span: span(character_start, self.offset),
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
                                span: span(character_start, self.offset),
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
                    span: span(start, self.input.len()),
                });
            };
            match byte {
                b'"' => {
                    self.offset += 1;
                    return Ok((Bytes::from(decoded), span(start, self.offset)));
                }
                b'\\' => {
                    let escape_start = self.offset;
                    self.offset += 1;
                    let Some(&escaped) = self.input.as_bytes().get(self.offset) else {
                        return Err(ParseError::InvalidBytes {
                            span: span(escape_start, self.offset),
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
                                    span: span(escape_start, self.input.len()),
                                });
                            };
                            if !hex.as_bytes().iter().all(u8::is_ascii_hexdigit) {
                                return Err(ParseError::InvalidBytes {
                                    span: span(escape_start, hex_end),
                                });
                            }
                            decoded.push(u8::from_str_radix(hex, 16).map_err(|_| {
                                ParseError::InvalidBytes {
                                    span: span(escape_start, hex_end),
                                }
                            })?);
                            self.offset = hex_end;
                        }
                        _ => {
                            return Err(ParseError::InvalidBytes {
                                span: span(escape_start, self.offset),
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
                        span: span(self.offset, end),
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
        if self.input[start..].starts_with("!(") {
            let Some(relative_end) = self.input[start + 2..].find(')') else {
                self.offset = self.input.len();
                return Err(ParseError::InvalidO256 {
                    span: span(start, self.input.len()),
                });
            };
            let end = start + 2 + relative_end + 1;
            let encoded = &self.input[start + 2..end - 1];
            let value = O256::from_base64(encoded).map_err(|_| ParseError::InvalidO256 {
                span: span(start, end),
            })?;
            self.offset = end;
            return Ok(Event::Atom {
                value: Atom::O256(value),
                span: span(start, end),
            });
        }
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
        let span = span(start, end);
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
                    span: span(self.offset, self.offset),
                })
            });
        };
        match byte {
            b'(' => {
                let span = span(self.offset, self.offset + 1);
                self.offset += 1;
                self.depth += 1;
                Some(Ok(Event::Open { span }))
            }
            b')' if self.depth == 0 => {
                let span = span(self.offset, self.offset + 1);
                self.done = true;
                Some(Err(ParseError::UnexpectedClose { span }))
            }
            b')' => {
                let span = span(self.offset, self.offset + 1);
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

/// The two delimiter spans attached to a parsed list.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ListSpan {
    /// Opening-parenthesis span.
    pub open: Span,
    /// Closing-parenthesis span.
    pub close: Span,
}

/// Storage and payload choices for an [`SExpr`].
pub trait Repr: Sized {
    /// Atomic payload exposed by this representation.
    type Atom;
    /// Metadata attached to an atom node.
    type AtomMeta;
    /// Metadata attached to a list node.
    type ListMeta;
    /// Concrete atom-node storage.
    type AtomNode: Clone + Debug + Eq + Hash + PartialEq;
    /// Concrete list-node storage.
    type ListNode: Clone + Debug + Eq + Hash + PartialEq;

    /// Borrows an atom node's payload.
    fn atom(node: &Self::AtomNode) -> &Self::Atom;
    /// Borrows an atom node's metadata.
    fn atom_meta(node: &Self::AtomNode) -> &Self::AtomMeta;
    /// Borrows a list node's metadata.
    fn list_meta(node: &Self::ListNode) -> &Self::ListMeta;
    /// Borrows a list node's children.
    fn list_items(node: &Self::ListNode) -> &[SExpr<Self>];
}

/// Arc-backed immutable representation parameterized by its payloads.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SharedRepr<AtomValue = Atom, AtomMeta = (), ListMeta = ()>(
    PhantomData<fn() -> AtomValue>,
    PhantomData<fn() -> AtomMeta>,
    PhantomData<fn() -> ListMeta>,
);

/// Atom node used by [`SharedRepr`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SharedAtomNode<AtomValue, Meta> {
    value: AtomValue,
    metadata: Meta,
}

/// List node used by [`SharedRepr`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SharedListNode<R: Repr> {
    metadata: R::ListMeta,
    items: Arc<[SExpr<R>]>,
}

impl<AtomValue, AtomMeta, ListMeta> Repr for SharedRepr<AtomValue, AtomMeta, ListMeta>
where
    AtomValue: Clone + Debug + Eq + Hash,
    AtomMeta: Clone + Debug + Eq + Hash,
    ListMeta: Clone + Debug + Eq + Hash,
{
    type Atom = AtomValue;
    type AtomMeta = AtomMeta;
    type ListMeta = ListMeta;
    type AtomNode = SharedAtomNode<AtomValue, AtomMeta>;
    type ListNode = SharedListNode<Self>;

    fn atom(node: &Self::AtomNode) -> &Self::Atom {
        &node.value
    }

    fn atom_meta(node: &Self::AtomNode) -> &Self::AtomMeta {
        &node.metadata
    }

    fn list_meta(node: &Self::ListNode) -> &Self::ListMeta {
        &node.metadata
    }

    fn list_items(node: &Self::ListNode) -> &[SExpr<Self>] {
        &node.items
    }
}

/// An immutable, cheaply cloned S-expression in representation `R`.
pub struct SExpr<R: Repr = SharedRepr>(Arc<SExprNode<R>>);

/// One layer of an [`SExpr`] template.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SExprNode<R: Repr = SharedRepr> {
    /// An atomic node.
    Atom(R::AtomNode),
    /// A proper-list node.
    List(R::ListNode),
}

impl<R: Repr> Clone for SExpr<R> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<R: Repr> Debug for SExpr<R>
where
    SExprNode<R>: Debug,
{
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl<R: Repr> PartialEq for SExpr<R>
where
    SExprNode<R>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<R: Repr> Eq for SExpr<R> where SExprNode<R>: Eq {}

impl<R: Repr> Hash for SExpr<R>
where
    SExprNode<R>: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

/// A parsed S-expression carrying source spans.
pub type SpannedRepr = SharedRepr<Atom, Span, ListSpan>;

/// The default shared representation without source metadata.
pub type ErasedRepr = SharedRepr<Atom, (), ()>;

/// A parsed S-expression carrying source spans.
pub type Expr = SExpr<SpannedRepr>;

/// The contents of a parsed [`Expr`].
pub type ExprKind = SExprNode<SpannedRepr>;

impl<R: Repr> SExpr<R> {
    /// Wraps one representation-specific node.
    #[must_use]
    pub fn from_node(node: SExprNode<R>) -> Self {
        Self(Arc::new(node))
    }

    /// Returns this expression's immutable contents.
    #[must_use]
    pub fn node(&self) -> &SExprNode<R> {
        &self.0
    }
}

impl<AtomValue, AtomMeta, ListMeta> SExpr<SharedRepr<AtomValue, AtomMeta, ListMeta>>
where
    AtomValue: Clone + Debug + Eq + Hash,
    AtomMeta: Clone + Debug + Eq + Hash,
    ListMeta: Clone + Debug + Eq + Hash,
{
    /// Creates an atom in the configurable shared representation.
    #[must_use]
    pub fn from_atom(value: AtomValue, metadata: AtomMeta) -> Self {
        Self::from_node(SExprNode::Atom(SharedAtomNode { value, metadata }))
    }

    /// Creates a list in the configurable shared representation.
    #[must_use]
    pub fn from_list(metadata: ListMeta, items: impl Into<Arc<[Self]>>) -> Self {
        Self::from_node(SExprNode::List(SharedListNode {
            metadata,
            items: items.into(),
        }))
    }
}

impl SExpr {
    /// Creates a spanless atomic expression.
    #[must_use]
    pub fn atom(value: Atom) -> Self {
        Self::from_atom(value, ())
    }

    /// Creates a spanless proper-list expression.
    #[must_use]
    pub fn list(items: impl Into<Arc<[Self]>>) -> Self {
        Self::from_list((), items)
    }
}

impl Expr {
    /// Creates an atomic expression.
    #[must_use]
    pub fn atom(value: Atom, span: Span) -> Self {
        Self::from_atom(value, span)
    }

    /// Creates a proper-list expression.
    #[must_use]
    pub fn list(open: Span, items: impl Into<Arc<[Self]>>, close: Span) -> Self {
        Self::from_list(ListSpan { open, close }, items)
    }

    /// Erases all source spans, preserving atoms and tree shape.
    ///
    /// # Panics
    ///
    /// Panics only if the internal iterative traversal fails to produce one
    /// output for its one input, which would be an implementation defect.
    #[must_use]
    pub fn erase(&self) -> SExpr {
        erase_expressions(core::slice::from_ref(self))
            .into_iter()
            .next()
            .expect("one input expression produces one output expression")
    }

    /// Traverses this expression as a balanced event stream without recursion.
    #[must_use]
    pub fn events(&self) -> Events<'_> {
        Events::expression(self)
    }
}

/// An immutable, cheaply cloned sequence of top-level expressions.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Document(Arc<[Expr]>);

impl Document {
    /// Creates a document from top-level expressions.
    #[must_use]
    pub fn new(expressions: impl Into<Arc<[Expr]>>) -> Self {
        Self(expressions.into())
    }

    /// Returns the top-level expressions.
    #[must_use]
    pub fn expressions(&self) -> &[Expr] {
        &self.0
    }

    /// Traverses this document as an event stream without recursion.
    #[must_use]
    pub fn events(&self) -> Events<'_> {
        Events::document(self)
    }

    /// Erases every source span from this document.
    #[must_use]
    pub fn erase(&self) -> SDocument {
        SDocument::new(erase_expressions(self.expressions()))
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
                Event::Atom { value, span } => Expr::atom(value, span),
                Event::Close { span } => {
                    let Some(frame) = frames.pop() else {
                        return Err(StructureError::UnexpectedCloseEvent { span });
                    };
                    Expr::list(frame.open, frame.items, span)
                }
            };
            if let Some(frame) = frames.last_mut() {
                frame.items.push(expression);
            } else {
                roots.push(expression);
            }
        }
        if let Some(frame) = frames.first() {
            return Err(StructureError::UnterminatedListEvents {
                open: frame.open.clone(),
            });
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

/// An immutable, cheaply cloned spanless S-expression document.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct SDocument(Arc<[SExpr]>);

impl SDocument {
    /// Creates a spanless document.
    #[must_use]
    pub fn new(expressions: impl Into<Arc<[SExpr]>>) -> Self {
        Self(expressions.into())
    }

    /// Returns the document's top-level expressions.
    #[must_use]
    pub fn expressions(&self) -> &[SExpr] {
        &self.0
    }
}

fn erase_expressions(expressions: &[Expr]) -> Vec<SExpr> {
    enum Pending<'a> {
        Visit(&'a Expr),
        FinishList(usize),
    }

    let mut pending = expressions
        .iter()
        .rev()
        .map(Pending::Visit)
        .collect::<Vec<_>>();
    let mut values = Vec::new();
    while let Some(item) = pending.pop() {
        match item {
            Pending::Visit(expression) => match expression.node() {
                ExprKind::Atom(node) => {
                    values.push(SExpr::<ErasedRepr>::atom(SpannedRepr::atom(node).clone()));
                }
                ExprKind::List(node) => {
                    let items = SpannedRepr::list_items(node);
                    pending.push(Pending::FinishList(items.len()));
                    pending.extend(items.iter().rev().map(Pending::Visit));
                }
            },
            Pending::FinishList(child_count) => {
                let first = values.len() - child_count;
                let children = values.drain(first..).collect::<Vec<_>>();
                values.push(SExpr::<ErasedRepr>::list(children));
            }
        }
    }
    values
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
            pending: document.0.iter().rev().map(Pending::Expr).collect(),
        }
    }
}

impl Iterator for Events<'_> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pending.pop()? {
            Pending::Close(span) => Some(Event::Close { span }),
            Pending::Expr(expression) => match expression.node() {
                ExprKind::Atom(node) => Some(Event::Atom {
                    value: SpannedRepr::atom(node).clone(),
                    span: SpannedRepr::atom_meta(node).clone(),
                }),
                ExprKind::List(node) => {
                    let metadata = SpannedRepr::list_meta(node);
                    let items = SpannedRepr::list_items(node);
                    self.pending.push(Pending::Close(metadata.close.clone()));
                    self.pending.extend(items.iter().rev().map(Pending::Expr));
                    Some(Event::Open {
                        span: metadata.open.clone(),
                    })
                }
            },
        }
    }
}

impl FusedIterator for Events<'_> {}

/// Opinionated width-aware S-expression layout.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Printer {
    /// Preferred maximum line width.
    pub width: usize,
    /// Spaces used when a list breaks across lines.
    pub indent: isize,
}

impl Default for Printer {
    fn default() -> Self {
        Self {
            width: 80,
            indent: 2,
        }
    }
}

impl Printer {
    /// Formats one expression, choosing flat or broken list layouts by width.
    ///
    /// # Errors
    ///
    /// Returns an error if an externally constructed atom cannot be represented
    /// by the fixed concrete grammar while retaining its atom kind.
    pub fn expression(self, expression: &Expr) -> Result<String, PrintError> {
        self.events(expression.events())
    }

    /// Formats every expression in a document, one root per line.
    ///
    /// # Errors
    ///
    /// Returns an error if an externally constructed atom cannot be represented
    /// by the fixed concrete grammar while retaining its atom kind.
    pub fn document(self, document: &Document) -> Result<String, PrintError> {
        self.events(document.events())
    }

    fn events(self, events: impl IntoIterator<Item = Event>) -> Result<String, PrintError> {
        let mut frames: Vec<Vec<RcDoc<'static>>> = Vec::new();
        let mut roots = Vec::new();
        for event in events {
            let document = match event {
                Event::Open { .. } => {
                    frames.push(Vec::new());
                    continue;
                }
                Event::Atom { value, .. } => RcDoc::text(atom_text(&value)?),
                Event::Close { .. } => {
                    let children = frames
                        .pop()
                        .expect("AST traversal always emits balanced events");
                    if children.is_empty() {
                        RcDoc::text("()")
                    } else {
                        RcDoc::text("(")
                            .append(RcDoc::intersperse(children, RcDoc::line()).nest(self.indent))
                            .append(")")
                            .group()
                    }
                }
            };
            match frames.last_mut() {
                Some(frame) => frame.push(document),
                None => roots.push(document),
            }
        }
        let document = RcDoc::intersperse(roots, RcDoc::hardline());
        let mut output = String::new();
        document
            .render_fmt(self.width, &mut output)
            .expect("rendering into a String cannot fail");
        Ok(output)
    }
}

/// Why an owned atom cannot be printed without changing its lexical kind.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("{kind} value {value:?} is not representable in S-expression syntax"))]
pub struct PrintError {
    /// Atom kind being rendered.
    pub kind: &'static str,
    /// Invalid in-memory spelling.
    pub value: SmolStr,
}

fn bare(value: &str) -> bool {
    !value.is_empty()
        && !value
            .chars()
            .any(|character| character.is_whitespace() || matches!(character, '(' | ')' | ';'))
}

fn atom_text(atom: &Atom) -> Result<String, PrintError> {
    let checked = |kind, value: &SmolStr, valid: bool| {
        valid.then(|| value.to_string()).ok_or_else(|| PrintError {
            kind,
            value: value.clone(),
        })
    };
    match atom {
        Atom::Symbol(value) => checked(
            "symbol",
            value,
            bare(value)
                && !value.starts_with([':', '#', '"'])
                && !value.starts_with("b\"")
                && !value.as_bytes()[0].is_ascii_digit(),
        ),
        Atom::String(value) => Ok(encode_string(value)),
        Atom::Bytes(value) => Ok(Atom::encode_bytes(value)),
        Atom::Number(value) => checked(
            "number",
            value,
            bare(value) && value.as_bytes().first().is_some_and(u8::is_ascii_digit),
        ),
        Atom::Keyword(value) => {
            checked("keyword", value, bare(value)).map(|value| format!(":{value}"))
        }
        Atom::Directive(value) => {
            checked("directive", value, bare(value)).map(|value| format!("#{value}"))
        }
        Atom::O256(value) => Ok(Atom::encode_o256(*value)),
    }
}

fn encode_string(value: &str) -> String {
    let mut encoded = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => encoded.push_str("\\\\"),
            '"' => encoded.push_str("\\\""),
            '\n' => encoded.push_str("\\n"),
            '\r' => encoded.push_str("\\r"),
            '\t' => encoded.push_str("\\t"),
            '\0' => encoded.push_str("\\0"),
            other => encoded.push(other),
        }
    }
    encoded.push('"');
    encoded
}

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
    let actual = document.expressions().len();
    if actual != 1 {
        return Err(OneError::Count { actual });
    }
    document
        .expressions()
        .first()
        .cloned()
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
