//! A small streaming textual S-expression dialect.
//!
//! Lists use parentheses. Atoms are either bare non-whitespace text excluding
//! `(`, `)`, `"`, and `;`, or double-quoted text. Quoted atoms support `\\`,
//! `\"`, `\n`, `\r`, and `\t`. A semicolon starts a line comment outside a
//! quoted atom. The parser yields borrowed atoms unless escapes require a new
//! allocation.

use std::borrow::Cow;
use std::fmt;

use crate::{Symbol, sax::Event};

/// A streaming parser over UTF-8 S-expression text.
#[derive(Clone, Debug)]
pub struct Parser<'a> {
    input: &'a str,
    offset: usize,
    depth: usize,
    finished: bool,
}

/// A text syntax error with its UTF-8 byte offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    offset: usize,
    kind: ErrorKind,
}

/// The category of a text syntax error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A closing parenthesis has no matching opening parenthesis.
    UnexpectedListEnd,
    /// Input ended with open lists.
    UnclosedList,
    /// Input ended inside a quoted atom.
    UnterminatedQuotedAtom,
    /// A quoted atom contains an unsupported escape.
    InvalidEscape,
}

impl Error {
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
        write!(formatter, "{:?} at byte {}", self.kind, self.offset)
    }
}

impl std::error::Error for Error {}

/// Parses `input` into a lazy SAX event stream.
#[must_use]
pub const fn parse(input: &str) -> Parser<'_> {
    Parser {
        input,
        offset: 0,
        depth: 0,
        finished: false,
    }
}

/// Parses `input` into events using the crate's default owned atom type.
///
/// Use [`parse`] when borrowed atoms are preferable. This adapter copies
/// borrowed atoms and transfers already-decoded quoted atoms into [`Symbol`].
pub fn parse_symbols(input: &str) -> impl Iterator<Item = Result<Event, Error>> + '_ {
    parse(input).map(|result| {
        result.map(|event| {
            event.map(|atom| match atom {
                Cow::Borrowed(text) => Symbol::new(text),
                Cow::Owned(text) => Symbol::from(text),
            })
        })
    })
}

impl<'a> Parser<'a> {
    fn error(&mut self, offset: usize, kind: ErrorKind) -> Result<Event<Cow<'a, str>>, Error> {
        self.finished = true;
        Err(Error { offset, kind })
    }

    fn skip_trivia(&mut self) {
        loop {
            let rest = &self.input[self.offset..];
            let whitespace = rest
                .char_indices()
                .find(|(_, character)| !character.is_whitespace())
                .map_or(rest.len(), |(index, _)| index);
            self.offset += whitespace;

            if self.input[self.offset..].starts_with(';') {
                self.offset += self.input[self.offset..]
                    .find('\n')
                    .unwrap_or(self.input.len() - self.offset);
            } else {
                break;
            }
        }
    }

    fn quoted(&mut self) -> Result<Event<Cow<'a, str>>, Error> {
        let quote = self.offset;
        self.offset += 1;
        let content = self.offset;
        let mut decoded = None::<String>;

        while self.offset < self.input.len() {
            let rest = &self.input[self.offset..];
            let character = rest.chars().next().expect("non-empty remainder");
            match character {
                '"' => {
                    let end = self.offset;
                    self.offset += 1;
                    return Ok(Event::Atom(match decoded {
                        Some(value) => Cow::Owned(value),
                        None => Cow::Borrowed(&self.input[content..end]),
                    }));
                }
                '\\' => {
                    let escape_offset = self.offset;
                    let output =
                        decoded.get_or_insert_with(|| self.input[content..self.offset].into());
                    self.offset += 1;
                    let Some(escaped) = self.input[self.offset..].chars().next() else {
                        return Err(Error {
                            offset: quote,
                            kind: ErrorKind::UnterminatedQuotedAtom,
                        });
                    };
                    let decoded_character = match escaped {
                        '\\' => '\\',
                        '"' => '"',
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        _ => {
                            return Err(Error {
                                offset: escape_offset,
                                kind: ErrorKind::InvalidEscape,
                            });
                        }
                    };
                    output.push(decoded_character);
                    self.offset += escaped.len_utf8();
                }
                _ => {
                    if let Some(output) = &mut decoded {
                        output.push(character);
                    }
                    self.offset += character.len_utf8();
                }
            }
        }

        Err(Error {
            offset: quote,
            kind: ErrorKind::UnterminatedQuotedAtom,
        })
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<Event<Cow<'a, str>>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        self.skip_trivia();

        if self.offset == self.input.len() {
            self.finished = true;
            return if self.depth == 0 {
                None
            } else {
                Some(Err(Error {
                    offset: self.offset,
                    kind: ErrorKind::UnclosedList,
                }))
            };
        }

        match self.input.as_bytes()[self.offset] {
            b'(' => {
                self.offset += 1;
                self.depth += 1;
                Some(Ok(Event::ListStart))
            }
            b')' if self.depth == 0 => Some(self.error(self.offset, ErrorKind::UnexpectedListEnd)),
            b')' => {
                self.offset += 1;
                self.depth -= 1;
                Some(Ok(Event::ListEnd))
            }
            b'"' => match self.quoted() {
                Ok(event) => Some(Ok(event)),
                Err(error) => {
                    self.finished = true;
                    Some(Err(error))
                }
            },
            _ => {
                let start = self.offset;
                let end = self.input[start..]
                    .char_indices()
                    .find(|(_, character)| {
                        character.is_whitespace() || matches!(character, '(' | ')' | '"' | ';')
                    })
                    .map_or(self.input.len(), |(index, _)| start + index);
                self.offset = end;
                Some(Ok(Event::Atom(Cow::Borrowed(&self.input[start..end]))))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::{ErrorKind, parse, parse_symbols};
    use crate::{Symbol, sax::Event};

    #[test]
    fn parser_streams_structure_comments_and_atoms() {
        let events = parse("(alpha ; ignored\n (\"beta gamma\" \"line\\nfeed\"))")
            .collect::<Result<Vec<_>, _>>()
            .expect("valid input");
        assert_eq!(
            events,
            [
                Event::ListStart,
                Event::Atom(Cow::Borrowed("alpha")),
                Event::ListStart,
                Event::Atom(Cow::Borrowed("beta gamma")),
                Event::Atom(Cow::Owned(String::from("line\nfeed"))),
                Event::ListEnd,
                Event::ListEnd,
            ]
        );
    }

    #[test]
    fn parser_reports_offsets_and_stops_after_an_error() {
        let parser = parse("(a)");
        assert!(parser.into_iter().all(|event| event.is_ok()));

        let error = parse(")").next().expect("one result").expect_err("invalid");
        assert_eq!(error.kind(), ErrorKind::UnexpectedListEnd);
        assert_eq!(error.offset(), 0);

        let error = parse("\"\\q\"")
            .next()
            .expect("one result")
            .expect_err("invalid");
        assert_eq!(error.kind(), ErrorKind::InvalidEscape);
        assert_eq!(error.offset(), 1);
    }

    #[test]
    fn parser_adapts_to_default_owned_symbols() {
        let events = parse_symbols("(alpha \"beta\\ngamma\")")
            .collect::<Result<Vec<_>, _>>()
            .expect("valid input");
        assert_eq!(
            events,
            [
                Event::ListStart,
                Event::Atom(Symbol::new("alpha")),
                Event::Atom(Symbol::new("beta\ngamma")),
                Event::ListEnd,
            ]
        );
    }
}
