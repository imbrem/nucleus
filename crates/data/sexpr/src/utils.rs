//! Resource-bounded parsing and canonical text emission.
//!
//! These adapters compose the [`crate::sax`] and [`crate::text`] modules. They
//! do not introduce a second tree or event representation.

use std::fmt;

use crate::{
    SExpr,
    sax::{BuildError, Event, EventWriter, FromEvents, ToEvents},
    text,
};

/// Resource limits applied while parsing and constructing an owned expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseLimits {
    /// Maximum number of SAX events, including list delimiters.
    pub events: usize,
    /// Maximum number of simultaneously open lists.
    pub depth: usize,
    /// Maximum total UTF-8 bytes across all atoms.
    pub atom_bytes: usize,
}

impl ParseLimits {
    /// Creates a limit set.
    #[must_use]
    pub const fn new(events: usize, depth: usize, atom_bytes: usize) -> Self {
        Self {
            events,
            depth,
            atom_bytes,
        }
    }
}

/// The resource whose parsing limit was exceeded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    /// SAX event count.
    Events,
    /// Simultaneously open list count.
    Depth,
    /// Total UTF-8 bytes across atoms.
    AtomBytes,
}

/// An error parsing text into an owned expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// The input is not valid in the crate's textual dialect.
    Syntax(text::Error),
    /// The event stream does not contain exactly one balanced expression.
    Structure(BuildError),
    /// A caller-selected resource limit was exceeded.
    Limit {
        /// The exhausted resource.
        resource: Resource,
        /// The configured inclusive limit.
        limit: usize,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax(error) => write!(formatter, "invalid S-expression text: {error}"),
            Self::Structure(error) => write!(formatter, "invalid S-expression structure: {error}"),
            Self::Limit { resource, limit } => {
                write!(formatter, "{resource:?} limit of {limit} exceeded")
            }
        }
    }
}

impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Syntax(error) => Some(error),
            Self::Structure(error) => Some(error),
            Self::Limit { .. } => None,
        }
    }
}

/// Parses one expression into the default owned [`crate::Symbol`]
/// representation.
///
/// Limits are checked before an event is retained. `atom_bytes` counts decoded
/// UTF-8, so escape spelling cannot disguise the size of the constructed tree.
///
/// # Errors
///
/// Returns syntax, structure, or resource-limit errors without conflating
/// their causes.
pub fn parse_symbols(input: &str, limits: ParseLimits) -> Result<SExpr, ParseError> {
    let mut events = Vec::new();
    let mut depth = 0usize;
    let mut atom_bytes = 0usize;

    for parsed in text::parse_symbols(input) {
        let event = parsed.map_err(ParseError::Syntax)?;
        if events.len() == limits.events {
            return Err(ParseError::Limit {
                resource: Resource::Events,
                limit: limits.events,
            });
        }

        match &event {
            Event::ListStart => {
                depth = depth.checked_add(1).ok_or(ParseError::Limit {
                    resource: Resource::Depth,
                    limit: limits.depth,
                })?;
                if depth > limits.depth {
                    return Err(ParseError::Limit {
                        resource: Resource::Depth,
                        limit: limits.depth,
                    });
                }
            }
            Event::Atom(atom) => {
                atom_bytes =
                    atom_bytes
                        .checked_add(atom.as_bytes().len())
                        .ok_or(ParseError::Limit {
                            resource: Resource::AtomBytes,
                            limit: limits.atom_bytes,
                        })?;
                if atom_bytes > limits.atom_bytes {
                    return Err(ParseError::Limit {
                        resource: Resource::AtomBytes,
                        limit: limits.atom_bytes,
                    });
                }
            }
            Event::ListEnd => depth -= 1,
        }
        events.push(event);
    }

    SExpr::from_events(events).map_err(ParseError::Structure)
}

struct TextWriter<'a, W> {
    output: &'a mut W,
    /// Whether each open list already contains a child.
    lists: Vec<bool>,
    wrote_root: bool,
}

impl<W: fmt::Write> TextWriter<'_, W> {
    fn before_value(&mut self) -> fmt::Result {
        if let Some(has_child) = self.lists.last_mut() {
            if *has_child {
                self.output.write_char(' ')?;
            }
            *has_child = true;
        } else {
            debug_assert!(!self.wrote_root, "ToEvents emitted multiple roots");
            self.wrote_root = true;
        }
        Ok(())
    }

    fn atom(&mut self, atom: &str) -> fmt::Result {
        if is_bare(atom) {
            return self.output.write_str(atom);
        }

        self.output.write_char('"')?;
        for character in atom.chars() {
            match character {
                '\\' => self.output.write_str("\\\\")?,
                '"' => self.output.write_str("\\\"")?,
                '\n' => self.output.write_str("\\n")?,
                '\r' => self.output.write_str("\\r")?,
                '\t' => self.output.write_str("\\t")?,
                character => self.output.write_char(character)?,
            }
        }
        self.output.write_char('"')
    }
}

impl<A, W> EventWriter<A> for TextWriter<'_, W>
where
    A: AsRef<str> + ?Sized,
    W: fmt::Write,
{
    type Error = fmt::Error;

    fn write(&mut self, event: Event<&A>) -> Result<(), Self::Error> {
        match event {
            Event::ListStart => {
                self.before_value()?;
                self.output.write_char('(')?;
                self.lists.push(false);
            }
            Event::Atom(atom) => {
                self.before_value()?;
                self.atom(atom.as_ref())?;
            }
            Event::ListEnd => {
                debug_assert!(self.lists.pop().is_some(), "ToEvents emitted unmatched end");
                self.output.write_char(')')?;
            }
        }
        Ok(())
    }
}

fn is_bare(atom: &str) -> bool {
    !atom.is_empty()
        && atom.chars().all(|character| {
            !character.is_whitespace() && !matches!(character, '(' | ')' | '"' | ';')
        })
}

/// Writes one value in the canonical form of the crate's textual dialect.
///
/// Canonical output uses one space between siblings and quotes an atom exactly
/// when it cannot be represented bare.
///
/// # Errors
///
/// Returns the destination's [`fmt::Error`].
pub fn write_text<T, W>(value: &T, output: &mut W) -> fmt::Result
where
    T: ToEvents,
    T::Atom: AsRef<str>,
    W: fmt::Write,
{
    value.write_events(&mut TextWriter {
        output,
        lists: Vec::new(),
        wrote_root: false,
    })
}

/// Returns one value in the canonical form of the crate's textual dialect.
///
/// # Panics
///
/// Panics only if writing to an in-memory [`String`] unexpectedly reports a
/// formatting error.
#[must_use]
pub fn to_text<T>(value: &T) -> String
where
    T: ToEvents,
    T::Atom: AsRef<str>,
{
    let mut output = String::new();
    write_text(value, &mut output).expect("writing to String is infallible");
    output
}

#[cfg(test)]
mod tests {
    use crate::{SExpr, Symbol};

    use super::{ParseError, ParseLimits, Resource, parse_symbols, to_text};

    const GENEROUS: ParseLimits = ParseLimits::new(100, 10, 1_000);

    #[test]
    fn symbols_round_trip_through_canonical_text() {
        let expression = SExpr::list(vec![
            SExpr::atom(Symbol::new("bare")),
            SExpr::atom(Symbol::new("")),
            SExpr::atom(Symbol::new("white space")),
            SExpr::atom(Symbol::new("non\u{a0}breaking")),
            SExpr::atom(Symbol::new("quote\"slash\\line\n")),
            SExpr::list(vec![SExpr::atom(Symbol::new("λ"))]),
        ]);

        let text = to_text(&expression);
        assert_eq!(
            text,
            "(bare \"\" \"white space\" \"non\u{a0}breaking\" \"quote\\\"slash\\\\line\\n\" (λ))"
        );
        assert_eq!(parse_symbols(&text, GENEROUS).unwrap(), expression);
    }

    #[test]
    fn every_limit_is_inclusive_and_reported_separately() {
        assert!(parse_symbols("(a)", ParseLimits::new(3, 1, 1)).is_ok());

        assert!(matches!(
            parse_symbols("(a)", ParseLimits::new(2, 1, 1)),
            Err(ParseError::Limit {
                resource: Resource::Events,
                limit: 2
            })
        ));
        assert!(matches!(
            parse_symbols("(())", ParseLimits::new(4, 1, 0)),
            Err(ParseError::Limit {
                resource: Resource::Depth,
                limit: 1
            })
        ));
        assert!(matches!(
            parse_symbols("\"a\\nb\"", ParseLimits::new(1, 0, 2)),
            Err(ParseError::Limit {
                resource: Resource::AtomBytes,
                limit: 2
            })
        ));
    }

    #[test]
    fn syntax_and_structure_errors_remain_distinct() {
        assert!(matches!(
            parse_symbols("(a", GENEROUS),
            Err(ParseError::Syntax(_))
        ));
        assert!(matches!(
            parse_symbols("a b", GENEROUS),
            Err(ParseError::Structure(_))
        ));
    }
}
